TS Studio Android - Decoration Set Selected cap 100

Patch for the ANDROID source project. It does not modify the separate Windows/desktop Python app.

Copy the files in this archive into the root of your Android project, preserving their paths:
- app/src/main/assets/app.js: Decoration rows and Set selected now explicitly support up to 100.
- app/src/main/python/android_engine.py: Android Decoration descriptor exposes max=100.
- app/src/main/python/desktop_logic.py: Android save logic validates and verifies Decoration quantities through 100.
- tests/test_engine.py: regression test for 100 accepted and 101 rejected.

Then commit/push the changed files and run your GitHub Actions APK workflow. Install the newly built APK; an already installed APK will still have its previous UI.
