# TS Studio Android friend cache patch

This patch updates the Android source only. It does not include any profile records from the supplied TSVIP archive.

## Changes

- Saves a profile to the app-private `profile_cache.json` after TS Studio successfully fetches that city with FetchCity.
- Adds **Build Profile Cache** to the Send Card and Clone V1/V3 friend pickers. It fetches up to the selected limit (default 100), traverses up to depth 2, reuses saved donor XML, logs progress, and supports the existing Stop button.
- Adds unique City ID counts and group filters for All, Profiles Cache, Followed Friends, Random Friends, Last Random Friends, Last Help, Clan Members, Followers, and New Friends.
- Reads matching relationship groups from LocalInfo, including LastRandomFriends and LastHelp variants.
- Adds tests for deduplicated group counts and cache creation after a successful FetchCity.

## Apply to the existing repository

1. Download and extract this ZIP into the root of the existing TSStudioAndroid GitHub repository, allowing the `app/` and `tests/` paths to be replaced.
2. Commit and push to the repository's `main` branch. The existing `Build TS Studio APK` GitHub Actions workflow runs the Python test suite, builds the APK, verifies its signature, and uploads the APK as an Actions artifact.
3. Download `TS-Studio-2.0-Android.apk` from the completed workflow's Artifacts section and install it on the rooted device/emulator.
4. Connect to Township, open Send Card or Clone V1/V3, and select a group. Use **Build Profile Cache** to fetch new profiles. The process writes each successful profile immediately to TS Studio's private app storage; it is independent of TSVIP.

The cache lives inside TS Studio's app-private storage. Clearing TS Studio's app data clears that cache; it can be rebuilt from the LocalInfo friend network.
