import unittest,sys,tempfile,base64,json,copy,subprocess,zipfile,io,re,shlex
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'app/src/main/python'))
import android_engine as E
B,D=E.B,E.D
KINDS=('avatar','skin','stickers','profile','achievements','decoration','barn','zoo','tutorial','advantages','quantities','academy','market','regatta','pass','train','clone1','clone3','send')
def fixture():
 pair=B.read_account_backup_bytes(base64.b64decode(D.GUI_LV3_TEMPLATE_DATA))[:2];game,local=map(B.decode_save,pair)
 game=re.sub(rb'<ZooInfo\b[^>]*Paddocks[^>]*/>',b'',game)
 blocks={'AndroidTestProfile':b'<AndroidTestProfile><DataElem name="UnlockedAvatars" value="" type="string"/></AndroidTestProfile>',
 'SeasonTicket':b'<SeasonTicket premium="0" score="1"><Vars/><FreeRoad><Stage score="1" extra="keep"><Reward type="ST_Chest" count="1"><Unknown flag="keep"/><SubReward type="Brick" count="2" mystery="keep"/></Reward></Stage><Stage score="2"><Reward type="Glass" count="3"/></Stage></FreeRoad><PremiumRoad><Stage score="396"><Reward type="Brick" count="4"/></Stage></PremiumRoad></SeasonTicket>',
 'RegataCenter':b'<RegataCenter><Regata><FreeTask id="Match3_win_1" num="2" ver="1"/><Vars/></Regata></RegataCenter>',
 'Trains':b'<Trains><Object v="'+B.xml_escape_attribute(json.dumps({'productId_1':'Wheat','productCount_1':2,'productId_2':'Corn','productCount_2':4,'cardPack1':'CardC_Pack1','untouched':'yes'})).encode()+b'"/></Trains>',
 'ZooInfo':b'<ZooInfo Paddocks="'+B.xml_escape_attribute(json.dumps({'list':[{'type':next(iter(B.TSVIP_ZOO_ANIMALS)),'members':[{'piecesCount':0,'status':0}]}]})).encode()+b'"/>',
 'AndroidTestObjects':b'<AndroidTestObjects><Object v="'+B.xml_escape_attribute(json.dumps({'storeId':'citymarket','slotsCount':8})).encode()+b'"/><Object v="'+B.xml_escape_attribute(json.dumps({'storeId':'bagfactory','slotsCount':3,'keep':42})).encode()+b'"/></AndroidTestObjects>'}
 for name,block in blocks.items():game=B._clone_upsert_root_block(game,name,block)
 return B.encode_save(game,pair[0]),B.encode_save(local,pair[1])
class Launcher(unittest.TestCase):
 def test_launch_uses_native_package_manager_event_when_bridge_exists(self):
  original_event,original_shell,original_package=E.EVENT,E.root_shell,B.PACKAGE_NAME
  events=[];calls=[];E.EVENT=events.append;E.root_shell=lambda *a,**k:calls.append(a) or b'';B.PACKAGE_NAME='com.playrix.township.vn'
  try:E.launch_game()
  finally:E.EVENT=original_event;E.root_shell=original_shell;B.PACKAGE_NAME=original_package
  self.assertEqual(calls,[]);self.assertEqual(json.loads(events[0]),{'event':'launch','package':'com.playrix.township.vn'})
 def test_apply_autolaunches_only_after_write_succeeds(self):
  original=(E.CONFIG,E.CONNECTED,E.EVENT,E.write_pair,E.encoded_pair,E.state,E.BASELINE,B.PACKAGE_NAME)
  events=[];E.CONFIG={'package':'com.playrix.township.vn','launch':True};E.CONNECTED=True;E.EVENT=events.append;E.write_pair=lambda pair,expected:None;E.encoded_pair=lambda:(b'game',b'local');E.state=lambda:{'connected':True};E.BASELINE=('baseline-game','baseline-local');B.PACKAGE_NAME='com.playrix.township.vn'
  try:result=json.loads(E.request('apply'))
  finally:E.CONFIG,E.CONNECTED,E.EVENT,E.write_pair,E.encoded_pair,E.state,E.BASELINE,B.PACKAGE_NAME=original
  self.assertTrue(result['ok'],result);self.assertEqual(json.loads(events[-1]),{'event':'launch','package':'com.playrix.township.vn'})
 def test_uses_android_activity_manager_instead_of_monkey(self):
  original=E.root_shell;calls=[];E.root_shell=lambda command,timeout=45:calls.append(command) or b'Starting activity'
  try:E.launch_game()
  finally:E.root_shell=original
  self.assertEqual(len(calls),1)
  self.assertEqual(shlex.split(calls[0]),['am','start','-a','android.intent.action.MAIN','-c','android.intent.category.LAUNCHER','-p','com.playrix.township.vn'])
class Editors(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.pair=fixture()
 def setUp(self):self.tmp=tempfile.TemporaryDirectory();E.initialize(self.tmp.name);E.commit_pair(*self.pair)
 def tearDown(self):self.tmp.cleanup()
 def test_all_editor_descriptions(self):
  for k in KINDS:
   with self.subTest(kind=k):json.dumps(E.describe(k))
 def test_connect_gate_and_stale_revision(self):
  before=E.snapshot();r=json.loads(E.request('edit',json.dumps({'kind':'land','revision':-1})));self.assertFalse(r['ok']);self.assertEqual(before,E.snapshot())
  E.CONNECTED=False;self.assertRaises(B.SaveToolError,E.describe,'barn')
 def test_codec_modes_and_invalid_xml(self):
  xml='<root><Global><Var name="townName" v="Thành phố 🌷"/></Global></root>'.encode()
  for compress in (True,False):
   out=D.gui_encode_xml_standalone(xml,compress);self.assertEqual(B.decode_save(out),B.canonical_xml(xml));self.assertNotEqual(int.from_bytes(out[4:8],'little'),0)
  self.assertRaises(Exception,D.gui_encode_xml_standalone,b'<root>broken')
 def test_level_pair_and_undo(self):
  before=E.snapshot();E.edit('profile_stats',{'values':{'level':2,'cash':456,'coin':789}});g,l=map(B.decode_save,E.encoded_pair())
  self.assertEqual(B.read_township_level(g),2);self.assertEqual(B._clone_tag_attrs(l,'PushNotifDeviceInfo')['lvl'],'2');self.assertEqual(E.identities(*map(B.decode_save,self.pair)),E.identities(g,l));self.assertTrue(json.loads(E.request('undo'))['ok']);self.assertEqual(before,E.snapshot())
 def test_barn_decoration_quantities(self):
  old=B._advanced_read(B.SESSION.current_xml,'Glass');E.edit('barn',{'level':20,'values':{'Brick':123}});self.assertEqual(B._advanced_read(B.SESSION.current_xml,'Glass'),old);self.assertEqual(B._advanced_read(B.SESSION.current_xml,'Brick'),'123')
  E.edit('decoration',{'values':{'ExpeditionDecoration46':1}});E.edit('quantities',{'values':{'m3Bomb':17}});self.assertEqual(B._advanced_read(B.SESSION.current_xml,B.TSVIP_QUANTITIES['m3Bomb'][0]),'17')
 def test_decoration_quantity_cap_is_100(self):
  item='Apple_Garden';before=E.snapshot();E.edit('decoration',{'values':{item:100}})
  self.assertEqual(B.decoration_inventory(B.SESSION.current_xml)[item],100)
  before_invalid=E.snapshot()
  with self.assertRaises(B.SaveToolError):E.edit('decoration',{'values':{item:101}})
  self.assertEqual(E.snapshot(),before_invalid)
 def test_xml_catalog_extensions(self):
  skin='Skin_Train_future_76';E.edit('skin',{'values':{'Train':{skin:True}}})
  self.assertTrue(B.unlock_catalog_states(B.SESSION.current_xml,'skin','Train',[skin])[skin])
  for item in ('ExpeditionDecoration54','Merge2Decoration19'):
   E.edit('decoration',{'values':{item:2}})
   self.assertEqual(B.decoration_inventory(B.SESSION.current_xml)[item],2)
  self.assertIn('Skin_Cow_birthday2026',B.TSVIP_SKINS['Cow'])
  self.assertNotIn('Skin_TrainStation_lunarN',B.TSVIP_SKINS['TrainStation'])
  self.assertIn('DSoGUBNqXn8yEANUPic+FQhRUVwlEFs5JVUZKysUAD4=',B.TSVIP_PROFILE['UnlockedBadges'])
  self.assertGreater(len(B.TSVIP_PROFILE['UnlockedStyles']),7)
 def test_unlock_states_roundtrip(self):
  for state in (True,False):E.edit('avatar',{'values':{'398':state}});self.assertEqual(B.avatar_states(B.SESSION.current_xml)['398']['state'],state)
  for k,cat in [('skin',B.TSVIP_SKINS),('stickers',B.TSVIP_STICKERS),('profile',B.TSVIP_PROFILE),('achievements',{'Achievements':B.TSVIP_ACHIEVEMENTS})]:
   g=next(iter(cat));key=next(iter(cat[g]))
   for state in (True,False):E.edit(k,{'values':{g:{key:state}}});self.assertEqual(B.unlock_catalog_states(B.SESSION.current_xml,k,g,[key])[key],state)
 def test_academy_and_slots(self):
  E.edit('academy',{'values':{'Factory':{'bagfactory':{'bonuses':{'timeBonus':25,'moneyBonus':20,'xpBonus':15,'shelfBonus':1},'edited':['timeBonus']}}},'slots':{'bagfactory':6}})
  inv,_=D.gui_factory_slot_inventory(B.SESSION.current_xml);self.assertEqual(inv['bagfactory'][2]['slotsCount'],6);self.assertEqual(inv['bagfactory'][2]['keep'],42)
 def test_pass_preserves_unknown_and_unselected(self):
  before=D.pass_stage_models(B.SESSION.current_xml,'FreeRoad');after={k:v for k,v in copy.deepcopy(before[0]).items() if k!='raw'}
  for c in after['subs']:c.pop('raw',None)
  after['given']=True;after['subs'][0]['count']=99;E.edit('pass',{'values':{'FreeRoad':{'1':after}}});now=D.pass_stage_models(B.SESSION.current_xml,'FreeRoad')
  self.assertEqual(now[1]['raw'],before[1]['raw']);self.assertIn(b'mystery="keep"',now[0]['raw']);self.assertIn(b'<Unknown flag="keep"/>',now[0]['raw']);self.assertEqual(now[0]['subs'][0]['count'],99)
 def test_pass_removed_child_does_not_transfer_attributes(self):
  xml=B.SESSION.current_xml.replace(b'<SubReward type="Brick" count="2" mystery="keep"/>',b'<SubReward type="Brick" count="2" mystery="first"/><SubReward type="Glass" count="4" mystery="second"/>')
  E.stage(xml);after=E.describe('pass')['roads']['FreeRoad'][0];after['subs'].pop(0)
  E.edit('pass',{'values':{'FreeRoad':{'1':after}}});raw=D.pass_stage_models(B.SESSION.current_xml,'FreeRoad')[0]['raw']
  self.assertIn(b'mystery="second"',raw);self.assertNotIn(b'mystery="first"',raw)
 def test_train_scoped_edit(self):
  E.edit('train',{'values':{'1:1:1':{'productCount':25}}});data=D.gui_train_inventory(B.SESSION.current_xml,1)[0][1];self.assertEqual(data['productCount_1'],25);self.assertEqual(data['productCount_2'],4);self.assertEqual(data['untouched'],'yes')
 def test_market_zoo_advantages_regatta(self):
  E.edit('market',{'value':123});self.assertEqual(E.describe('market')['value'],123);E.edit('zoo',{'ids':[next(iter(B.TSVIP_ZOO_ANIMALS))]});self.assertEqual(B.zoo_card_inventory(B.SESSION.current_xml)[1]['list'][0]['members'][0]['piecesCount'],30);E.edit('advantages',{'values':{'SP_BoostStorageCapacity':50}});E.edit('regatta',{'value':3});self.assertEqual(E.describe('regatta')['value'],3)
 def test_clone_v3_identity(self):
  target=B.SESSION.current_xml;local=B.SESSION.localinfo_xml;donor=E.plain(B.set_township_level(target,2,True));g,l,_=B.clone_city_v3(target,donor,local);g,l=D.gui_preserve_v3_device(target,g,local,l);l=D.gui_sync_local_level(l,g);self.assertEqual(E.identities(target,local),E.identities(g,l));self.assertEqual(B.read_township_level(g),2)
 def test_backup_and_restore_stage(self):
  p=E.backup_pair(E.encoded_pair(),'test');self.assertEqual(B.read_account_backup(p)[:2],E.encoded_pair());E.edit('profile_stats',{'values':{'coin':42}});r=json.loads(E.request('restore',json.dumps({'path':str(p),'write':False})));self.assertTrue(r['ok']);self.assertEqual(B.SESSION.current_xml,B.decode_save(self.pair[0]))
 def test_zip_traversal_guard(self):
  stream=io.BytesIO()
  with zipfile.ZipFile(stream,'w') as z:z.writestr('../mGameInfo.xml',b'x')
  self.assertRaises(B.SaveToolError,B.read_account_backup_bytes,stream.getvalue())
 def test_send_key_required(self):self.assertRaises(B.SaveToolError,B.prepare_send_card,'sender','recipient',1,'a',1,1,'token')
class Transport(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.pair=fixture()
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();E.initialize(self.tmp.name);E.commit_pair(*self.pair);self.saved=(E.root_shell,E.stop_game,B.REMOTE_SAVE,B.REMOTE_LOCALINFO,E.set_package)
  E.set_package=lambda p:None;E.stop_game=lambda:None;folder=Path(self.tmp.name)/'device';folder.mkdir();B.REMOTE_SAVE=str(folder/'mGameInfo.xml');B.REMOTE_LOCALINFO=str(folder/'LocalInfo.xml')
  for path,data in zip((B.REMOTE_SAVE,B.REMOTE_LOCALINFO),self.pair):Path(path).write_bytes(data);Path(path+'.bak').write_bytes(data)
  def shell(command,timeout=45):
   p=subprocess.run(['sh','-c',command],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout)
   if p.returncode:raise B.SaveToolError(p.stderr.decode())
   return p.stdout
  E.root_shell=shell
 def tearDown(self):E.root_shell,E.stop_game,B.REMOTE_SAVE,B.REMOTE_LOCALINFO,E.set_package=self.saved;self.tmp.cleanup()
 def test_write_pair_readback(self):
  E.edit('profile_stats',{'values':{'coin':12345}});pair=E.encoded_pair();E.write_pair(pair,E.BASELINE);self.assertEqual(E.read_pair(),pair);self.assertEqual(Path(B.REMOTE_SAVE+'.bak').read_bytes(),pair[0])
 def test_stale_device_guard(self):
  Path(B.REMOTE_SAVE).write_bytes(self.pair[0]+b'changed');self.assertRaises(B.SaveToolError,E.write_pair,self.pair,E.BASELINE);self.assertTrue(Path(B.REMOTE_SAVE).read_bytes().endswith(b'changed'))
 def test_partial_failure_rollback(self):
  E.edit('profile_stats',{'values':{'level':2}});pair=E.encoded_pair();original=E.root_shell;count=0
  def fail(command,timeout=45):
   nonlocal count
   if command.startswith('mv -f ') and '.tsstudio-' in command:
    count+=1
    if count==3:raise B.SaveToolError('Injected write failure')
   return original(command,timeout)
  E.root_shell=fail;self.assertRaises(B.SaveToolError,E.write_pair,pair,E.BASELINE);self.assertEqual(E.read_pair(),self.pair);self.assertEqual(Path(B.REMOTE_SAVE+'.bak').read_bytes(),self.pair[0]);self.assertFalse(list((E.ROOT/'transactions').glob('*/pending.json')))
if __name__=='__main__':unittest.main()
