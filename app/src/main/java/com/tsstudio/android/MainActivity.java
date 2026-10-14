package com.tsstudio.android;
import android.app.Activity;
import android.os.Bundle;
import android.content.Intent;
import android.net.Uri;
import android.webkit.*;
import android.database.Cursor;
import android.provider.OpenableColumns;
import android.view.WindowManager;
import androidx.webkit.WebViewAssetLoader;
import androidx.documentfile.provider.DocumentFile;
import com.chaquo.python.Python;
import com.chaquo.python.PyObject;
import org.json.*;
import java.io.*;
import java.util.UUID;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;

public class MainActivity extends Activity {
 private WebView web; private PyObject engine; private File studio; private String pickerId,exportPath; private boolean destroyed=false;
 private final ExecutorService worker=Executors.newSingleThreadExecutor(),files=Executors.newSingleThreadExecutor();
 private final AtomicBoolean busy=new AtomicBoolean(false);
 private static final int OPEN=101,FOLDER=102,SAVE=103;
 @Override public void onCreate(Bundle state){
  super.onCreate(state);studio=new File(getFilesDir(),"studio");studio.mkdirs();web=new WebView(this);setContentView(web);
  WebSettings s=web.getSettings();s.setJavaScriptEnabled(true);s.setDomStorageEnabled(true);s.setAllowFileAccess(false);s.setAllowContentAccess(false);s.setMixedContentMode(WebSettings.MIXED_CONTENT_NEVER_ALLOW);s.setJavaScriptCanOpenWindowsAutomatically(false);
  WebViewAssetLoader loader=new WebViewAssetLoader.Builder().addPathHandler("/assets/",new WebViewAssetLoader.AssetsPathHandler(this)).build();
  web.setWebViewClient(new WebViewClient(){
   @Override public WebResourceResponse shouldInterceptRequest(WebView v,WebResourceRequest r){WebResourceResponse x=loader.shouldInterceptRequest(r.getUrl());return x!=null?x:new WebResourceResponse("text/plain","utf-8",new ByteArrayInputStream(new byte[0]));}
   @Override public boolean shouldOverrideUrlLoading(WebView v,WebResourceRequest r){return true;}
  });
  web.setWebChromeClient(new WebChromeClient());web.addJavascriptInterface(new Bridge(),"Android");web.loadUrl("https://appassets.androidplatform.net/assets/index.html");
 }
 private void emit(String raw){runOnUiThread(()->{if(!destroyed)web.evaluateJavascript("window.nativeMessage("+JSONObject.quote(raw)+")",null);});}
 private void reply(String id,boolean ok,Object data){try{emit(new JSONObject().put("id",id).put("ok",ok).put(ok?"data":"error",data).toString());}catch(JSONException ignored){}}
 public class Events {
  public void emit(String raw){
   try{
    JSONObject o=new JSONObject(raw);String event=o.optString("event");
    if(event.equals("backup")){String path=o.getString("path"),name=o.getString("name");files.execute(()->mirrorBackup(path,name));}
    else if(event.equals("launch")){String packageName=o.getString("package");runOnUiThread(()->launchPackage(packageName));return;}
   }catch(Exception ignored){}
   MainActivity.this.emit(raw);
  }
 }
 private void launchPackage(String packageName){
  try{
   Intent intent=getPackageManager().getLaunchIntentForPackage(packageName);
   if(intent==null){message("Save was written, but Android could not find a launcher activity for "+packageName,"warning");return;}
   intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK|Intent.FLAG_ACTIVITY_RESET_TASK_IF_NEEDED);
   startActivity(intent);message("Township launched: "+packageName,"info");
  }catch(Exception e){message("Save was written, but Township could not be launched: "+e.getMessage(),"warning");}
 }
 public class Bridge {
  @JavascriptInterface public void call(String action,String payload,String id){
   if(!busy.compareAndSet(false,true)){reply(id,false,"An operation is already running");return;}
   runOnUiThread(()->getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON));
   worker.execute(()->{try{
    if(engine==null){engine=Python.getInstance().getModule("android_engine");engine.callAttr("initialize",studio.getAbsolutePath(),new Events());}
    JSONObject r=new JSONObject(engine.callAttr("request",action,payload).toString()).put("id",id);emit(r.toString());
   }catch(Throwable e){reply(id,false,e.getMessage()==null?e.toString():e.getMessage());}
   finally{busy.set(false);runOnUiThread(()->getWindow().clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON));}});
  }
  @JavascriptInterface public void cancel(){if(engine!=null)engine.callAttr("cancel");}
  @JavascriptInterface public void browse(String id){runOnUiThread(()->{
   if(pickerId!=null){reply(id,false,"Finish the current file picker");return;}pickerId=id;
   Intent i=new Intent(Intent.ACTION_OPEN_DOCUMENT).setType("*/*").addCategory(Intent.CATEGORY_OPENABLE);
   String last=getPreferences(MODE_PRIVATE).getString("lastInput","");if(!last.isEmpty()&&android.os.Build.VERSION.SDK_INT>=26)i.putExtra("android.provider.extra.INITIAL_URI",Uri.parse(last));
   startActivityForResult(i,OPEN);
  });}
  @JavascriptInterface public void backupFolder(String id){runOnUiThread(()->{
   if(pickerId!=null){reply(id,false,"Finish the current file picker");return;}pickerId=id;
   Intent i=new Intent(Intent.ACTION_OPEN_DOCUMENT_TREE).addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION|Intent.FLAG_GRANT_WRITE_URI_PERMISSION|Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION);startActivityForResult(i,FOLDER);
  });}
  @JavascriptInterface public void exportFile(String path,String name,String id){runOnUiThread(()->{try{
   owned(path);if(pickerId!=null)throw new IOException("Finish the current file picker");pickerId=id;exportPath=path;
   startActivityForResult(new Intent(Intent.ACTION_CREATE_DOCUMENT).addCategory(Intent.CATEGORY_OPENABLE).setType(name.endsWith(".zip")?"application/zip":"application/octet-stream").putExtra(Intent.EXTRA_TITLE,name),SAVE);
  }catch(Exception e){reply(id,false,e.getMessage());}});}
 }
 private File owned(String path)throws IOException{File f=new File(path).getCanonicalFile();if(!f.isFile()||!f.getPath().startsWith(studio.getCanonicalPath()+File.separator))throw new IOException("Invalid app file");return f;}
 private void copy(InputStream in,OutputStream out)throws IOException{
  if(in==null||out==null)throw new IOException("Cannot open document stream");byte[] b=new byte[65536];long total=0;int n;
  while((n=in.read(b))!=-1){total+=n;if(total>64L*1024*1024)throw new IOException("File exceeds 64 MB");out.write(b,0,n);}out.flush();
 }
 private void mirrorBackup(String path,String name){String tree=getPreferences(MODE_PRIVATE).getString("backupTree","");if(tree.isEmpty())return;DocumentFile child=null;
  try{DocumentFile dir=DocumentFile.fromTreeUri(this,Uri.parse(tree));if(dir==null||!dir.canWrite())throw new IOException("Choose a writable backup folder in Settings");child=dir.createFile("application/zip",name);if(child==null)throw new IOException("Cannot create backup document");
   try(InputStream in=new FileInputStream(owned(path));OutputStream out=getContentResolver().openOutputStream(child.getUri(),"w")){copy(in,out);}message("Backup copied to selected folder.","info");
  }catch(Exception e){if(child!=null)child.delete();message("External backup failed; internal backup is kept. "+e.getMessage(),"warning");}
 }
 private void message(String text,String level){try{emit(new JSONObject().put("event","log").put("data",new JSONObject().put("time","").put("level",level).put("text",text)).toString());}catch(JSONException ignored){}}
 @Override protected void onActivityResult(int code,int result,Intent data){super.onActivityResult(code,result,data);String id=pickerId;pickerId=null;if(id==null)return;
  if(result!=RESULT_OK||data==null||data.getData()==null){reply(id,true,JSONObject.NULL);return;}Uri uri=data.getData();
  if(code==FOLDER){try{if((data.getFlags()&Intent.FLAG_GRANT_WRITE_URI_PERMISSION)==0)throw new IOException("Choose a writable backup folder");getContentResolver().takePersistableUriPermission(uri,Intent.FLAG_GRANT_READ_URI_PERMISSION|Intent.FLAG_GRANT_WRITE_URI_PERMISSION);getPreferences(MODE_PRIVATE).edit().putString("backupTree",uri.toString()).apply();reply(id,true,uri.toString());}catch(Exception e){reply(id,false,e.getMessage());}return;}
  String output=exportPath;files.execute(()->{try{
   if(code==SAVE){try(InputStream in=new FileInputStream(owned(output));OutputStream out=getContentResolver().openOutputStream(uri,"w")){copy(in,out);}reply(id,true,"Saved");return;}
   String name="import.xml";try(Cursor c=getContentResolver().query(uri,new String[]{OpenableColumns.DISPLAY_NAME},null,null,null)){if(c!=null&&c.moveToFirst())name=c.getString(0);}
   name=name.replaceAll("[^\\p{L}\\p{N}._-]","_");if(name.length()>100)name=name.substring(name.length()-100);File folder=new File(studio,"imports");folder.mkdirs();File target=new File(folder,UUID.randomUUID()+"_"+name);
   try(InputStream in=getContentResolver().openInputStream(uri);OutputStream out=new FileOutputStream(target)){copy(in,out);}catch(Exception e){target.delete();throw e;}
   getPreferences(MODE_PRIVATE).edit().putString("lastInput",uri.toString()).apply();reply(id,true,new JSONObject().put("path",target.getAbsolutePath()).put("name",name));
  }catch(Exception e){reply(id,false,e.getMessage());}});
 }
 @Override public void onBackPressed(){web.evaluateJavascript("window.handleBack()",null);}
 @Override protected void onDestroy(){destroyed=true;super.onDestroy();worker.shutdown();files.shutdown();web.destroy();}
}
