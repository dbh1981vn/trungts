import ast,base64,zlib,pathlib,json,hashlib,sys
root=pathlib.Path(__file__).resolve().parents[1];out=root/'app/src/main/python';s=pathlib.Path(sys.argv[1]).read_text();tree=ast.parse(s);a={x.id:n for n in tree.body if isinstance(n,ast.Assign) for x in n.targets if isinstance(x,ast.Name)}
core=zlib.decompress(base64.b85decode(ast.literal_eval(a['ENGINE_DATA'].value)));(out/'township_core.py').write_bytes(core)
functions=set('gui_catalog_list_field gui_write_profile_state gui_set_avatar_states gui_set_catalog_states gui_set_decoration_quantities gui_academy_inventory gui_set_academy_rows pass_stage_models pass_patch_stage pass_apply_rows gui_tsvip_content_checksum gui_encode_xml_standalone gui_convert_save_file barn_groups gui_factory_slot_inventory gui_set_factory_slots gui_train_scan gui_train_groups gui_train_inventory gui_edit_train_wagons gui_copy_donor_level gui_sync_local_level gui_preserve_v3_device gui_pair_level_report gui_newtown_identity gui_prepare_lv3_pair gui_design_metadata gui_design_spans gui_design_block gui_design_availability gui_design_version_check gui_clone_v1 gui_read_design_source'.split())
constants=set('THEME_FIELDS THEMES PROFILE LANGUAGES ACADEMY_FIELDS ACADEMY_NAMES PASS_REWARD_GROUPS PASS_REWARD_LABELS STICKER_VI_LABELS CONFIRMED_DECORATION_FRAGMENTS GUI_LV3_TEMPLATE_DATA DESIGN_GROUPS DESIGN_LABELS DESIGN_BLOCKS DESIGN_PROFILE'.split())
parts=['# Pure logic extracted from TS Studio v1.39. No Qt dependency.','import re,json,base64,zlib,os,uuid','from pathlib import Path','from datetime import datetime','from functools import lru_cache','import township_core as B']
for n in tree.body:
 if (isinstance(n,ast.FunctionDef) and n.name in functions) or (isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id in constants for x in n.targets)):parts.append(ast.get_source_segment(s,n))
parts += ["B.DECORATION_GROUPS={k:tuple(v) for k,v in B.DECORATION_GROUPS.items()}","B.DECORATION_GROUPS['special']+=tuple(k for k in CONFIRMED_DECORATION_FRAGMENTS if k not in B.DECORATION_GROUPS['special'])","B.DECORATION_FRAGMENTS=dict(B.DECORATION_FRAGMENTS,**CONFIRMED_DECORATION_FRAGMENTS)"]
(out/'desktop_logic.py').write_text('\n\n'.join(parts));cat={};codes=ast.literal_eval(a['I18N_CODES'].value)
for line in ast.literal_eval(a['I18N_DATA'].value).strip().splitlines():
 p=line.split('|');v=dict(zip(codes,p[1:]));v['vi']=p[0];cat[p[0]]=v;cat[v['en']]=v
(root/'app/src/main/assets/translations.js').write_text('window.TRANSLATIONS='+json.dumps(cat,ensure_ascii=False)+';')
(root/'docs/source-manifest.json').write_text(json.dumps({'desktop_sha256':hashlib.sha256(s.encode()).hexdigest(),'core_sha256':hashlib.sha256(core).hexdigest(),'pure_functions':sorted(functions)},indent=2))
