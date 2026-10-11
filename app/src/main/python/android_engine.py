"""Android JSON API; original v1.39 XML and codec implementation retained."""
import os,re,json,time,uuid,shlex,subprocess,threading,hashlib,base64,copy
from pathlib import Path
from datetime import datetime
import township_core as B
import desktop_logic as D
ROOT=None; CONFIG={}; CONNECTED=False; REVISION=0; BASELINE=None; UNDO=[]; LOGS=[]; EVENT=None; SU=None
CANCEL=threading.Event()
def log(text,level='info'):
 r={'time':datetime.now().strftime('%H:%M:%S'),'level':level,'text':str(text)};LOGS.append(r);del LOGS[:-1000]
 if EVENT:
  try:EVENT(json.dumps({'event':'log','data':r},ensure_ascii=False))
  except Exception:pass
B.print=lambda *a,**k:log(' '.join(map(str,a)))
def initialize(directory,event=None):
 global ROOT,CONFIG,EVENT
 ROOT=Path(directory).resolve();ROOT.mkdir(parents=True,exist_ok=True);EVENT=event.emit if event else None
 old=B.WORK_DIR
 for k,v in list(vars(B).items()):
  if isinstance(v,Path):
   try:setattr(B,k,ROOT/v.relative_to(old))
   except ValueError:pass
 B.WORK_DIR=ROOT
 for d in ('backups','a_TS_Files','imports','exports','transactions'):(ROOT/d).mkdir(exist_ok=True)
 CONFIG={'package':'com.playrix.township.vn','launch':False,'language':'en','theme':'pastel','colors':{},'backupFolder':''}
 if (ROOT/'settings.json').exists():CONFIG.update(json.loads((ROOT/'settings.json').read_text()))
 set_package(CONFIG['package']);log('TS Studio Android · Connect to load both saves.')
def set_package(package):
 if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)+',package) or package=='com.tsstudio.android':raise ValueError('Invalid Township package')
 B.PACKAGE_NAME=package;B.REMOTE_SAVE=f'/data/data/{package}/saves/mGameInfo.xml';B.REMOTE_LOCALINFO=f'/data/data/{package}/saves/LocalInfo.xml'
def q(s):return shlex.quote(str(s))
def root_shell(command,timeout=45):
 global SU
 if SU is None:
  for prefix in (['su','-c'],['su','0','sh','-c']):
   try:
    p=subprocess.run(prefix+['id -u'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=20)
    if p.returncode==0 and p.stdout.strip()==b'0':SU=prefix;break
   except (OSError,subprocess.TimeoutExpired):pass
  if SU is None:raise B.SaveToolError('Grant TS Studio root permission in Magisk / SuperSU, then Connect again.')
 p=subprocess.run(SU+[command],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout)
 if p.returncode:raise B.SaveToolError('Root operation failed: '+p.stderr.decode('utf-8','replace')[:500])
 return p.stdout
def stop_game():root_shell('am force-stop '+q(B.PACKAGE_NAME))
def launch_game():root_shell('am start -a android.intent.action.MAIN -c android.intent.category.LAUNCHER -p '+q(B.PACKAGE_NAME))
def launch_after_commit():
 try:launch_game()
 except Exception as err:log('Both XML files were written and verified, but Township could not be launched automatically: '+str(err),'warning')
def read_remote(path):
 size=int(root_shell('stat -c %s '+q(path)).strip())
 if not 0<size<=B.MAX_CONTAINER_SIZE:raise B.SaveToolError('Save size outside supported range')
 return root_shell('cat '+q(path))
def read_pair():return read_remote(B.REMOTE_SAVE),read_remote(B.REMOTE_LOCALINFO)
def digest(data):return hashlib.sha256(data).hexdigest()
def identities(game,local):
 m,_=B.parse_localinfo_metadata(local)
 return (B._clone_field_value(game,'cityId'),B._clone_field_value(game,'gameId'),m.get('own_city_id'),m.get('game_id'),m.get('token'))
def validate_pair(g,l):
 gx,lx=B.decode_save(g),B.decode_save(l);B.validate_xml_document(gx,'mGameInfo');B.validate_xml_document(lx,'LocalInfo');return gx,lx
def commit_pair(g,l):
 global CONNECTED,BASELINE,REVISION,UNDO
 gx,lx=validate_pair(g,l);s=B.SESSION
 s.original_container=g;s.original_xml=gx;s.current_xml=gx;s.localinfo_container=l;s.localinfo_xml=lx
 s.localinfo_meta,s.friends=B.parse_localinfo_metadata(lx);s.pending_localinfo_xml=None;s.pending_pair_templates=None;s.source_label=B.PACKAGE_NAME
 CONNECTED=True;BASELINE=tuple(map(digest,(g,l)));REVISION+=1;UNDO=[]
def require():
 if not CONNECTED:raise B.SaveToolError('Connect first')
def snapshot():
 s=B.SESSION;return s.current_xml,s.pending_localinfo_xml,s.pending_pair_templates
def stage(game,local=None,templates=None):
 global REVISION
 B.validate_xml_document(game,'Edited mGameInfo')
 if local is not None:B.validate_xml_document(local,'Edited LocalInfo')
 UNDO.append(snapshot());del UNDO[:-10];B.SESSION.current_xml=game
 if local is not None:B.SESSION.pending_localinfo_xml=local
 if templates is not None:B.SESSION.pending_pair_templates=templates
 REVISION+=1;log('Changes staged. Apply (Write to Game) to commit.')
def encoded_pair():
 s=B.SESSION;t=s.pending_pair_templates or (s.original_container,s.localinfo_container);gx=s.current_xml;lx=s.pending_localinfo_xml or s.localinfo_xml
 g,l=B.encode_save(gx,t[0]),B.encode_save(lx,t[1])
 if B.decode_save(g)!=B.canonical_xml(gx) or B.decode_save(l)!=B.canonical_xml(lx):raise B.SaveToolError('Pair codec verification failed')
 return g,l
def backup_pair(pair,label):
 p=B.create_account_backup(*pair,label=label);log('Backup verified: '+p.name)
 if EVENT:
  try:EVENT(json.dumps({'event':'backup','path':str(p),'name':p.name}))
  except Exception:pass
 return p
def durable(path,data):
 path=Path(path);tmp=path.with_suffix('.tmp')
 with tmp.open('wb') as f:f.write(data);f.flush();os.fsync(f.fileno())
 os.replace(tmp,path)
 fd=os.open(str(path.parent),os.O_RDONLY)
 try:os.fsync(fd)
 finally:os.close(fd)
def prepare_remote(local,remote,temp):
 root_shell('set -e\ncp -p '+q(remote)+' '+q(temp)+'\ncat '+q(local)+' > '+q(temp)+'\nctx=$(ls -Zd '+q(remote)+" | awk '{print $1}')\ncase \"$ctx\" in u:*) chcon \"$ctx\" "+q(temp)+';; esac\n')
 if read_remote(temp)!=Path(local).read_bytes():raise B.SaveToolError('Staging readback failed')
def rollback_journal(path):
 j=json.loads(path.read_text());set_package(j['package']);stop_game()
 for row in j['files']:
  temp=row['remote']+'.tsrestore';prepare_remote(row['backup'],row['remote'],temp);root_shell('mv -f '+q(temp)+' '+q(row['remote']))
  if read_remote(row['remote'])!=Path(row['backup']).read_bytes():raise B.SaveToolError('Rollback verification failed')
 root_shell('sync');path.rename(path.with_suffix('.recovered'));log('Interrupted write recovered; Township remains stopped.','warning')
def recover():
 for p in sorted((ROOT/'transactions').glob('*/pending.json')):rollback_journal(p)
 set_package(CONFIG['package'])
def write_pair(pair,expected=None):
 global CONNECTED
 stop_game();live=read_pair()
 if expected is not None and tuple(map(digest,live))!=expected:raise B.SaveToolError('Game saves changed since Connect. Reconnect before applying; staged changes are retained.')
 validate_pair(*pair);backup_pair(live,'before Android Apply');folder=ROOT/'transactions'/uuid.uuid4().hex;folder.mkdir();rows=[]
 for i,(remote,old,new) in enumerate(zip((B.REMOTE_SAVE,B.REMOTE_LOCALINFO),live,pair)):
  for suffix in ('','.bak'):
   target=remote+suffix
   if suffix and not root_shell('if [ -f '+q(target)+' ]; then echo yes; fi').strip():continue
   backup=folder/f'{i}{suffix}.original';output=folder/f'{i}{suffix}.new';durable(backup,old if not suffix else read_remote(target));durable(output,new)
   rows.append({'remote':target,'backup':str(backup),'output':str(output),'staged':target+'.tsstudio-'+folder.name})
 journal=folder/'pending.json';durable(journal,json.dumps({'package':B.PACKAGE_NAME,'files':rows}).encode())
 try:
  for r in rows:prepare_remote(r['output'],r['remote'],r['staged'])
  for r in rows:root_shell('mv -f '+q(r['staged'])+' '+q(r['remote']))
  root_shell('sync')
  for r in rows:
   if read_remote(r['remote'])!=Path(r['output']).read_bytes():raise B.SaveToolError('Write verification failed')
  journal.rename(folder/'complete.json')
 except Exception:
  try:rollback_journal(journal)
  except Exception as err:CONNECTED=False;log('Recovery incomplete. Do not launch Township. Connect to recover: '+str(err),'error')
  raise
 finally:
  for r in rows:
   try:root_shell('rm -f '+q(r['staged']))
   except Exception:pass
 commit_pair(*pair);log('Both saves written and verified. Check the results inside Township.')
def safe_input(path):
 p=Path(path).resolve()
 if not p.is_relative_to(ROOT) or not p.is_file():raise ValueError('Choose a file using Browse')
 if p.stat().st_size>B.MAX_CONTAINER_SIZE:raise ValueError('File exceeds 64 MB')
 return p
def plain(result):return result[0] if isinstance(result,tuple) else result
def profile_rows():
 rows=[];xml=B.SESSION.current_xml;readers={'level':B.read_township_level,'m3':B.read_match3_level,'win':B.read_first_win,'lives':B.read_lives,'mine':B.read_mine_depth}
 for icon,label,key,var,low,high in D.PROFILE:
  try:v=int(B.read_var(xml,var)['v']) if var else readers[key](xml) if key in readers else next((v for v in B.read_profile_stat(xml,key).values() if v is not None),None)
  except (ValueError,KeyError,B.SaveToolError):v=None
  rows.append(dict(id=key,label=label,icon=icon,value=v,min=low,max=high))
 try:date=datetime.fromtimestamp(int(B.read_var(xml,'gameStartDate')['v']),B.UTC_PLUS_7).strftime('%Y-%m')
 except Exception:date=''
 return {'rows':rows,'date':date}
def state():
 data=dict(connected=CONNECTED,revision=REVISION,settings=CONFIG,themes=D.THEMES,languages=D.LANGUAGES)
 if CONNECTED:
  s=B.SESSION;data.update(changed=s.changed or s.pending_localinfo_xml is not None,account=B.backup_account_info(s.current_xml,s.pending_localinfo_xml or s.localinfo_xml),profile=profile_rows())
 return data
def row(id,label=None,value=0,group='',**kw):return dict(id=str(id),label=str(label or id),value=value,group=group,**kw)
def describe(kind):
 require();xml=B.SESSION.current_xml;rows=[]
 if kind=='avatar':return {'mode':'states','rows':[row(k,'Avatar '+k,v['state'] is True,disabled=v['state'] is not None and type(v['state']) is not bool) for k,v in B.avatar_states(xml).items()]}
 if kind in ('skin','stickers','profile','achievements'):
  cats={'skin':B.TSVIP_SKINS,'stickers':B.TSVIP_STICKERS,'profile':B.TSVIP_PROFILE,'achievements':{'Achievements':tuple(B.TSVIP_ACHIEVEMENTS)}}[kind]
  for group,ids in cats.items():
   states=B.unlock_catalog_states(xml,kind,group,ids)
   for i,key in enumerate(ids):
    names=B.PROFILE_ITEM_LABELS.get(group,()) if kind=='profile' else ()
    label=names[i] if i<len(names) else D.STICKER_VI_LABELS.get(str(key),str(key)) if kind=='stickers' and CONFIG['language']=='vi' else str(key)
    rows.append(row(key,label,states[key],group))
  return {'mode':'states','rows':rows}
 if kind=='decoration':
  inv=B.decoration_inventory(xml)
  for g,ids in B.DECORATION_GROUPS.items():rows += [row(k,value=inv.get(k,0),group=g,min=0,max=20) for k in ids]
 elif kind=='barn':
  for g,ids in D.barn_groups(B.TSVIP_BARN_PRODUCTS).items():rows += [row(k,value=int(B._advanced_read(xml,B.barn_product_field(k)) or 0),group=g) for k in ids]
  return {'mode':'values','rows':rows,'level':int(B._advanced_read(xml,'WareHouseCashUpgrade') or 0)}
 elif kind=='zoo':
  _,data=B.zoo_card_inventory(xml);present={v.get('type') for v in data['list'] if isinstance(v,dict)}
  return {'mode':'select','rows':[row(k,v,disabled=k not in present) for k,v in B.TSVIP_ZOO_ANIMALS.items()]}
 elif kind=='tutorial':return {'mode':'select','rows':[row(k,v['label']) for k,v in B.TSVIP_TUTORIAL_FIXES.items()]}
 elif kind=='advantages':
  season=B._advanced_block(xml,'SeasonTicket')
  for k,default in B.TSVIP_ADVANTAGES.items():
   tags=B._level_field_tags(season,k);v=B.parse_attributes(tags[0].group()).get('v','0') if len(tags)==1 else '0'
   if k=='SP_BoostMineRocket':v=B._advanced_read(xml,'DiggingPremiumLevel') or '0'
   rows.append(row(k,value=int(v),suggested=default))
  return {'mode':'values','rows':rows,'mineDays':True}
 elif kind=='quantities':
  for k,(f,*_) in B.TSVIP_QUANTITIES.items():rows.append(row(k,B.TSVIP_QUANTITY_LABELS.get(k,k),int(B._advanced_read(xml,f) or 0),'Items'))
  for k in B.TSVIP_COUPONS:rows.append(row(k,B.TSVIP_QUANTITY_LABELS.get(k,k),group='Coupons'))
  for k in ('lives_inf_days','booster2x_days','currency_provider_amount','train_journey_amount','star','match3_moves'):rows.append(row(k,B.TSVIP_QUANTITY_LABELS.get(k,k),group='Other',max=36500 if k.endswith('_days') else 2147483647))
 elif kind=='academy':
  inv=D.gui_academy_inventory(xml)
  for g,items in B.TSVIP_ACADEMY.items():
   for k,template in items.items():
    old=inv.get((g,k),{});fields=[dict(id=f,label=label,max=limit,value=int(old.get('probability2' if f=='products' else f,0))) for f,label,limit in D.ACADEMY_FIELDS[g] if g!='Factory' or f in template]
    rows.append(row(k,D.ACADEMY_NAMES.get(k,k),group=g,fields=fields))
  slots,problems=D.gui_factory_slot_inventory(xml)
  return {'mode':'academy','rows':rows,'slots':[row(k,D.ACADEMY_NAMES.get(k,k),v[2]['slotsCount'],min=2,max=7) for k,v in slots.items()],'problems':problems}
 elif kind=='market':
  items=[d for _,d in B._json_attribute_rows(xml) if d.get('storeId')=='citymarket' and 'slotsCount' in d]
  if len(items)!=1:raise B.SaveToolError('Save needs exactly one citymarket with slotsCount')
  return dict(mode='number',value=items[0]['slotsCount'],min=1,max=9999)
 elif kind=='regatta':
  _,_,tasks,old=B.regatta_task_inventory(xml);return dict(mode='number',value=old,min=0,max=10000,tasks=tasks)
 elif kind=='pass':
  season=B._advanced_block(xml,'SeasonTicket');attrs=B.parse_attributes(season.split(b'>',1)[0]+b'>');roads={}
  for road in ('FreeRoad','PremiumRoad'):
   if re.search(('<'+road+r'\b').encode(),season):
    roads[road]=[{k:v for k,v in model.items() if k!='raw'} for model in D.pass_stage_models(xml,road)]
    for model in roads[road]:
     for index,child in enumerate(model['subs']):child.pop('raw',None);child['sourceIndex']=index
  return dict(mode='pass',roads=roads,premium=int(attrs.get('premium',0)),score=int(attrs.get('score',0)),products=list(dict.fromkeys(['ST_Chest']+[k for ids in D.PASS_REWARD_GROUPS.values() for k in ids]+list(B.TSVIP_BARN_PRODUCTS))))
 elif kind=='train':
  groups,_=D.gui_train_groups(xml)
  for scope,g in enumerate(groups,1):
   for train,(_,data,_,_) in enumerate(g['rows'],1):
    for wagon in range(1,6):
     if f'productId_{wagon}' in data or f'productCount_{wagon}' in data:rows.append(row(f'{scope}:{train}:{wagon}',f'Train {train} · Wagon {wagon}',group=g['path'],fields=[dict(id=k,value=data.get(f'cardPack{wagon}' if k=='cardPack' else f'{k}_{wagon}','' if k in ('productId','cardPack') else 0),type='text' if k in ('productId','cardPack') else 'number') for k in ('productId','productCount','orderBlue','orderBlueTime','cardPack','productDone')]))
  if not rows:raise B.SaveToolError('No supported wagon data. Wait for a train to return in Township, exit game, then reconnect.')
  return dict(mode='train',rows=rows)
 elif kind in ('clone1','clone3'):return dict(mode='clone',choices=D.DESIGN_LABELS,friends=[dict(id=v.city_id,name=v.city_name,level=v.level) for v in (B.SESSION.friends or {}).values()],defaults={k:v for k,v in (B.SESSION.localinfo_meta or {}).items() if k in ('version','fver')})
 elif kind=='send':return dict(mode='send',defaults=B.send_card_defaults(xml,B.SESSION.pending_localinfo_xml or B.SESSION.localinfo_xml),friends=[dict(id=v.city_id,name=v.city_name) for v in (B.SESSION.friends or {}).values()])
 else:raise ValueError('Unknown editor')
 return dict(mode='values',rows=rows)
def edit(kind,args):
 require();s=B.SESSION;xml=s.current_xml;local=None;values=args.get('values',{})
 if kind=='profile_stats':
  for k,v in values.items():
   if k=='date':xml=plain(B.set_game_start_month(xml,*map(int,v.split('-'))));continue
   v=int(v)
   if k in ('cash','coin'):xml=plain(B.set_integer_var(xml,'moneyCash' if k=='cash' else 'money',v))
   elif k=='level':xml=plain(B.set_township_level(xml,v,True));local=D.gui_sync_local_level(s.pending_localinfo_xml or s.localinfo_xml,xml)
   elif k in ('m3','win','lives','mine'):xml=plain({'m3':B.set_match3_level,'win':B.set_first_win,'lives':B.set_lives,'mine':B.set_mine_depth}[k](xml,v))
   else:xml=plain(B.set_profile_stat(xml,k,v))
 elif kind in ('land','museum','all_cards','my_cards','golden_pass'):xml=plain({'land':B.unlock_land,'museum':B.unlock_museum,'all_cards':lambda x:B.update_owned_cards(x,True),'my_cards':lambda x:B.update_owned_cards(x,False),'golden_pass':B.unlock_golden_pass}[kind](xml))
 elif kind=='avatar':xml=plain(D.gui_set_avatar_states(xml,values))
 elif kind in ('skin','stickers','profile','achievements'):xml=plain(D.gui_set_catalog_states(xml,kind,values))
 elif kind=='decoration':xml=plain(D.gui_set_decoration_quantities(xml,values))
 elif kind=='barn':
  if 'level' in args:xml=B.set_barn_level(xml,int(args['level']))
  for k,v in values.items():xml=B.set_barn_products(xml,[k],int(v))
 elif kind=='zoo':xml=B.set_zoo_cards(xml,args['ids'])
 elif kind=='tutorial':xml=B.fix_tutorial_categories(xml,args['ids'])
 elif kind=='advantages':xml=B.set_advantages(xml,values,args.get('mineDays'))
 elif kind=='quantities':xml=B.set_quantities(xml,values)
 elif kind=='market':xml=B.set_market_slots(xml,int(args['value']))
 elif kind=='regatta':xml=B.set_regatta_tasks(xml,int(args['value']))
 elif kind=='academy':
  if values:xml=plain(D.gui_set_academy_rows(xml,values))
  if args.get('slots'):xml=plain(D.gui_set_factory_slots(xml,args['slots']))
 elif kind=='train':
  for key,fields in values.items():scope,train,wagon=map(int,key.split(':'));xml=D.gui_edit_train_wagons(xml,train,[wagon],fields,scope)
 elif kind=='pass':
  changes={}
  for road,items in values.items():
   if road not in ('FreeRoad','PremiumRoad'):raise ValueError('Invalid road')
   current={r['index']:r for r in D.pass_stage_models(xml,road)};changes[road]={}
   for index,after in items.items():
    before=current[int(index)];after=copy.deepcopy(after);B._advanced_integer(after['count'],'Reward count')
    for pos,child in enumerate(after['subs']):
     B._advanced_integer(child['count'],'Chest count')
     source=child.pop('sourceIndex',pos)
     if source is not None:
      if not isinstance(source,int) or not 0<=source<len(before['subs']):raise ValueError('Invalid chest reward source')
      child['raw']=before['subs'][source]['raw']
    changes[road][int(index)]=(before,after)
  xml=D.pass_apply_rows(xml,changes)
  for k in ('premium','score'):
   if k in args:
    B._advanced_integer(args[k],k,1 if k=='premium' else 2147483647);season=B._advanced_block(xml,'SeasonTicket');end=season.index(b'>')+1;xml=B._decor_replace_block(xml,'SeasonTicket',B.replace_attribute(season[:end],k,str(args[k]))+season[end:])
 else:raise ValueError('Unknown edit')
 stage(xml,local)
def donor(args):
 if args.get('path'):return D.gui_read_design_source(safe_input(args['path']))
 city=args.get('city','').strip();m=B.SESSION.localinfo_meta or {};bv=args.get('bver') or m.get('version','');fv=args.get('fver') or m.get('fver','')
 if not re.fullmatch(r'[A-Za-z0-9_-]{3,64}',city):raise ValueError('Choose donor XML/ZIP or a valid City ID')
 if not re.fullmatch(r'\d+(?:\.\d+){1,3}',bv) or not re.fullmatch(r'\d+',fv):raise ValueError('Valid bver/fver from LocalInfo required')
 log('Fetching donor city…');return B.fetch_city_live(city,bv,fv,out_dir=B.FRIENDS_DIR/city)[0]
def clone(kind,args):
 source=donor(args);s=B.SESSION;note=D.gui_design_version_check(s.current_xml,source)
 if note:log(note,'warning')
 backup_pair(encoded_pair(),'before '+kind)
 if kind=='clone1':
  game,report,sync=D.gui_clone_v1(s.current_xml,source,args['ids'],args.get('copyLevel',False));local=D.gui_sync_local_level(s.pending_localinfo_xml or s.localinfo_xml,game) if sync else None
 else:
  old=s.pending_localinfo_xml or s.localinfo_xml;game,local,report=B.clone_city_v3(s.current_xml,source,old,args.get('removeSecrets',True),args.get('keepAir',False));game,local=D.gui_preserve_v3_device(s.current_xml,game,old,local);local=D.gui_sync_local_level(local,game)
 stage(game,local);log('Clone staged: '+str(report))
def new_city(args):
 require();mode=args.get('mode','builtin')
 if mode in ('builtin','file'):
  pair=B.new_towncity_payload()[:2] if mode=='builtin' else B.read_account_backup(safe_input(args['path']))[:2];backup_pair(encoded_pair(),'before New City');gx,lx=validate_pair(*pair);stage(gx,lx,pair);return
 if mode not in ('auto','resume'):raise ValueError('Unknown mode')
 source=D.gui_read_design_source(safe_input(args['path'])) if args.get('path') else B.decode_save(B.read_account_backup_bytes(base64.b64decode(D.GUI_LV3_TEMPLATE_DATA))[0])
 if B.read_township_level(source)!=3:raise ValueError('A level 3 template is required')
 stop_game();live=read_pair();gx,lx=validate_pair(*live)
 if tuple(map(digest,live))!=BASELINE:raise B.SaveToolError('Save changed; reconnect before New City')
 backup_pair(encoded_pair(),'before New City edited');reset=B.new_towncity_payload()[:2];excluded={B._clone_field_value(B.decode_save(reset[0]),'cityId')}
 if mode=='auto':
  for k in ('Version','FVer'):
   if B._clone_field_value(gx,k)!=B._clone_field_value(source,k):raise B.SaveToolError('Template version differs. Select matching ZIP; no reset performed.')
  excluded.add(B._clone_field_value(gx,'cityId'));write_pair(reset,BASELINE)
 launch_game();log('Accept Agree in Township. Waiting for a genuine new identity…');deadline=time.monotonic()+max(60,min(600,int(args.get('timeout',180))));last=None;stable=0
 while time.monotonic()<deadline:
  if CANCEL.wait(3):raise B.SaveToolError('Stopped. Reconnect and Resume without resetting again.')
  try:
   pair=read_pair();g,l=validate_pair(*pair);ident=D.gui_newtown_identity(g,l)
   if ident[0] in excluded:continue
   stable=stable+1 if ident==last else 1;last=ident
   if stable>=2:break
  except B.SaveToolError:continue
 else:raise B.SaveToolError('Timed out. Accept Agree, reconnect and Resume; do not reset again.')
 stop_game();pair=read_pair()
 if D.gui_newtown_identity(*validate_pair(*pair))!=last:raise B.SaveToolError('Identity changed; reconnect')
 commit_pair(*pair);prepared=D.gui_prepare_lv3_pair(*pair,source)
 if CANCEL.is_set():raise B.SaveToolError('Cancelled before LV3 write')
 write_pair(prepared,BASELINE);launch_game()
def request(action,payload='{}'):
 global CONNECTED,REVISION,CONFIG
 args=json.loads(payload)
 try:
  if action=='state':result=state()
  elif action=='settings':
   if args.get('package',CONFIG['package'])!=CONFIG['package']:
    if CONNECTED and (B.SESSION.changed or B.SESSION.pending_localinfo_xml):raise B.SaveToolError('Undo or Apply before changing package')
    set_package(args['package']);CONNECTED=False
   CONFIG.update({k:v for k,v in args.items() if k in CONFIG});durable(ROOT/'settings.json',json.dumps(CONFIG).encode());result=state()
  elif action=='connect':
   if CONNECTED and (B.SESSION.changed or B.SESSION.pending_localinfo_xml):backup_pair(encoded_pair(),'before reconnect edits')
   CONNECTED=False;recover();stop_game();commit_pair(*read_pair());log('Connected · '+B.PACKAGE_NAME);result=state()
  elif action=='describe':result=describe(args['kind']);result['revision']=REVISION
  elif action in ('edit','clone'):
   require()
   if args.get('revision')!=REVISION:raise B.SaveToolError('Editor is stale. Reopen it.')
   (edit if action=='edit' else clone)(args['kind'],args);result=state()
  elif action=='donor_preview':
   require();source=donor(args);available,reasons=D.gui_design_availability(source,B.SESSION.current_xml);result=dict(account=D.gui_design_metadata(source),available=available,reasons=reasons)
  elif action=='apply':
   require();write_pair(encoded_pair(),BASELINE)
   if CONFIG['launch']:launch_after_commit()
   result=state()
  elif action=='undo':
   require()
   if not UNDO:raise B.SaveToolError('No edits to undo')
   B.SESSION.current_xml,B.SESSION.pending_localinfo_xml,B.SESSION.pending_pair_templates=UNDO.pop();REVISION+=1;result=state()
  elif action=='backup':
   require()
   if args.get('source')=='device':stop_game();pair=read_pair()
   else:pair=encoded_pair() if args.get('source')=='edited' else (B.SESSION.original_container,B.SESSION.localinfo_container)
   p=backup_pair(pair,'Android '+args.get('source','original'));result=dict(path=str(p),name=p.name)
  elif action=='history':
   require();result=[dict(path=str(p),name=p.name,account=p.parent.name,time=datetime.fromtimestamp(p.stat().st_mtime).isoformat(timespec='seconds')) for p in sorted(B.ACCOUNT_BACKUP_DIR.rglob('*.zip'),key=lambda p:p.stat().st_mtime,reverse=True)]
  elif action=='backup_info':
   _,_,meta,doc=B.read_account_backup(safe_input(args['path']));result=dict(account=meta,details=doc)
  elif action=='restore':
   require();pair=B.read_account_backup(safe_input(args['path']))[:2];backup_pair(encoded_pair(),'before History edits')
   if args.get('write'):
    stop_game();commit_pair(*read_pair());write_pair(pair,BASELINE)
    if CONFIG['launch']:launch_after_commit()
   else:gx,lx=validate_pair(*pair);stage(gx,lx,pair)
   result=state()
  elif action=='codec':
   require();src=safe_input(args['path']);dest=ROOT/'exports'/(src.stem+('_encoded' if args.get('encode') else '_decoded')+'_'+uuid.uuid4().hex[:6]+'.xml');D.gui_convert_save_file(src,dest,args.get('encode',False));result=dict(path=str(dest),name=dest.name)
  elif action=='send':
   require();key=bytes.fromhex(args.pop('masterKey','').strip());d=B.send_card_defaults(B.SESSION.current_xml,B.SESSION.pending_localinfo_xml or B.SESSION.localinfo_xml)
   p=B.prepare_send_card(sender=d['sender'],recipient=args['recipient'],card_number=int(args['card']),collection=args['collection'],end_time=int(args['end_time']),send_counter=int(args['counter']),token=d['token'],name=d['name'],pic=d['pic'],bver=d['bver'],fver=d['fver'],master_key=key);result=B.send_card_live(p,key);log('Send Cards request finished. Check Township.')
  elif action=='new_city':CANCEL.clear();new_city(args);result=state()
  elif action=='export_log':
   p=ROOT/'exports'/('activity_'+datetime.now().strftime('%Y%m%d_%H%M%S')+'.txt');p.write_text('\n'.join(f"{r['time']} [{r['level']}] {r['text']}" for r in LOGS));result=dict(path=str(p),name=p.name)
  else:raise ValueError('Unknown action')
  return json.dumps(dict(ok=True,data=result),ensure_ascii=False)
 except Exception as exc:log(str(exc),'error');return json.dumps(dict(ok=False,error=str(exc)),ensure_ascii=False)
def cancel():CANCEL.set()
