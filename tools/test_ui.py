"""UI smoke test with fixture bridge. Does not claim device / root verification."""
import json,pathlib,tempfile,sys
from playwright.sync_api import sync_playwright
root=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(root/'tests'))
from test_engine import E,fixture,KINDS
E.initialize(tempfile.mkdtemp());E.commit_pair(*fixture());data={'state':E.state(),'editors':{k:dict(E.describe(k),revision=E.REVISION) for k in KINDS}}
assets=root/'app/src/main/assets';browser=sys.argv[1];out=pathlib.Path(sys.argv[2]);out.mkdir(exist_ok=True)
with sync_playwright() as p:
 b=p.chromium.launch(executable_path=browser,headless=True,args=['--no-sandbox']);page=b.new_page(viewport={'width':393,'height':852});errors=[];page.on('pageerror',lambda e:errors.append(str(e)))
 page.route('**/*',lambda r:r.fulfill(path=str(assets/r.request.url.split('/')[-1])))
 page.add_init_script('window.FIXTURE='+json.dumps(data)+';window.CALLS=[];window.Android={call:(action,payload,id)=>{let args=JSON.parse(payload);CALLS.push([action,args]);let result=action===\"state\"?{...FIXTURE.state,connected:false}:action===\"describe\"?FIXTURE.editors[args.kind]:action===\"history\"?[]:FIXTURE.state;setTimeout(()=>nativeMessage(JSON.stringify({id,ok:true,data:result})),10)},cancel:()=>{},browse:()=>{},backupFolder:()=>{}}')
 page.goto('https://appassets.androidplatform.net/assets/index.html');page.wait_for_selector('body:not(.working)');assert page.locator('#workspace').is_hidden();assert page.locator('#welcome').count()==0;assert page.locator('#package').count()==0;page.screenshot(path=str(out/'connect.png'),full_page=True)
 page.locator('#connectButton').click();page.wait_for_selector('#workspace:not([hidden])');assert page.locator('#connectionStats').is_visible();assert page.locator('#cityId').inner_text()==str(data['state']['account']['city_id']);assert page.locator('#cityFver').inner_text()==str(data['state']['account']['fver']);assert page.locator('#cityLevel').inner_text()==str(data['state']['account']['level']);page.screenshot(path=str(out/'profile.png'),full_page=True)
 assert page.locator('#applyButton').inner_text()=='Write to game'
 page.locator('#tabs button').nth(2).click();page.locator('.card').filter(has_text='Existing trains and wagons').get_by_role('button').click();page.wait_for_selector('body:not(.working)');page.locator('.editrow details').first.evaluate('(e)=>e.open=true');page.locator('.editrow').first.locator('input[type=number]').first.fill('77');page.locator('#saveModal').click();page.wait_for_selector('#overlay[hidden]',state='attached');calls=page.evaluate('CALLS');assert calls[-1][1]['values']['1:1:1']['productCount']==77,calls[-1]
 for tab in (1,2,3,4):
  page.locator('#tabs button').nth(tab).click()
  for i in range(page.locator('.card').count()):
   name=page.locator('.cardTitle').nth(i).inner_text();action=page.locator('.card').nth(i).get_by_role('button');assert action.inner_text()=='Apply';action.click();page.wait_for_selector('body:not(.working)')
   if name in ('Land','Museum','All Card','My Card','Golden Pass'):
    assert page.locator('#overlay').is_hidden(),name
    call=page.evaluate('CALLS[CALLS.length-1]');assert call[0]=='edit' and call[1]['kind'] in ('land','museum','all_cards','my_cards','golden_pass'),call
    continue
   page.wait_for_selector('#overlay:not([hidden])')
   if name.endswith('Academy'):page.screenshot(path=str(out/'academy.png'))
   if 'Golden Pass Editor' in name:page.locator('.stage').first.evaluate('(e)=>e.open=true');page.screenshot(path=str(out/'pass.png'))
   page.locator('#closeModal').click()
 page.locator('#settingsButton').click();page.screenshot(path=str(out/'settings.png'));page.locator('#closeModal').click();assert not errors,errors;assert page.evaluate('document.documentElement.scrollWidth<=innerWidth');print('UI: all editors rendered, mobile layout fits, train payload correct, no JS errors.');b.close()
