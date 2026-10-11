# TS Studio Android 2.01

Ứng dụng Android root, dựa trên TS Studio Python v1.39 của người dùng. Backend XML gốc được trích xuất nguyên vẹn, giao diện Android mới dùng WebView nội bộ và Chaquopy. Không cần máy tính/ADB để sử dụng.

## Sử dụng

1. Cài APK, vào Settings chọn `com.playrix.township.vn` hoặc `com.playrix.township` (có thể nhập package khác).
2. Chọn thư mục backup. Bản sao nội bộ luôn được giữ; thư mục đã chọn nhận thêm bản ZIP qua Android Storage Access Framework.
3. Bấm Connect, cấp quyền root. Game sẽ dừng để đọc `/data/data/{package}/saves/mGameInfo.xml` và `LocalInfo.xml`.
4. Chọn tab/editor, sửa và Save để cập nhật phiên làm việc. Chưa Connect thì các tab bị ẩn.
5. Bấm Apply (Write to Game) để sao lưu, ghi hai file, đồng bộ `.bak` nếu có và kiểm tra dữ liệu đọc lại. Có thể bật tự mở game sau Apply.

Các tab Profile Statics, Unlock, Tool, Premium và VIP có các chức năng trong yêu cầu. Editor danh sách có tìm kiếm, lọc nhóm, chọn nhiều dòng; các dòng không chọn giữ nguyên. Theme gồm 15 bộ màu gốc và 8 màu tùy chỉnh. Có 12 lựa chọn ngôn ngữ, tái sử dụng bảng dịch desktop; các câu mới chưa có bản dịch dùng tiếng Anh.

## Điểm cần biết

- Tool Encode dùng encoder độc lập v1.39. Apply vẫn dùng container mẫu gốc như backend desktop.
- Clone V1/V3 giữ danh tính target và đồng bộ level LocalInfo. Donor có thể từ XML/ZIP hoặc FetchCity.
- Send Cards cần master AES key hợp lệ, token và cấu hình của tài khoản. Không tự sinh key và không tự gửi lại khi timeout.
- New City có mẫu TSVIP, ZIP riêng, Auto LV3 và Resume. Auto/Resume ghi trực tiếp sau xác nhận; người dùng bấm Agree trong game khi được yêu cầu. Không tự bịa City ID. Mẫu LV3 có sẵn giữ từ Python, chỉ dùng khi phiên bản phù hợp.
- History cho mở ZIP vào phiên hoặc khôi phục trực tiếp. Khôi phục cả identity của backup là hành vi có chủ đích, khác với Clone.
- Google Drive OAuth của PyQt/keyring không được chuyển nguyên sang Android. Có thể chọn file từ Drive qua bộ chọn tài liệu Android khi Drive cung cấp chức năng này. Không có hàng đợi OAuth desktop.
- Giữ TS Studio trong ứng dụng gần đây khi chạy New City; Android có thể dừng tiến trình nền. Khi gián đoạn, mở lại và Connect để phục hồi giao dịch, rồi dùng Resume nếu phù hợp.
- Android 7 trở lên, cần Android System WebView hiện đại. APK universal chứa ARM32/ARM64/x86/x86_64.
- Không đảm bảo server chấp nhận mọi chỉnh sửa. Kiểm tra encode/đọc lại khác với kiểm chứng bên trong Township.
- Hai file không thể đổi đồng thời bằng một rename. Ứng dụng có nhật ký giao dịch và rollback; nếu bị tắt giữa lúc ghi, mở lại và Connect để phục hồi trước khi mở game.

## Build trên GitHub, không cài công cụ trên máy

Tạo repository **Private** và bật README. Đưa toàn bộ nội dung thư mục dự án này vào root repository, bao gồm `.github/workflows/build-apk.yml`. Vào **Actions → Build TS Studio APK → Run workflow**. Khi job thành công, tải artifact **TS-Studio-2.0-Android**, giải nén lấy APK.

Build sử dụng JDK 17, Gradle 8.9, AGP 8.7.3, Chaquopy 16.1.0, Python 3.11, SDK 35/target 34. Workflow tự cài và kiểm tra chữ ký APK. APK debug được ký để cài thử, không phải bản phát hành Play Store.

Để các build sau cài đè được, giữ một debug keystore cố định ở secret `TSSTUDIO_KEYSTORE_BASE64` (alias androiddebugkey, password android). Nếu không cấu hình, mỗi runner có thể sinh khóa khác; khi đổi khóa Android sẽ không cho cập nhật đè. Không commit keystore vào repository. Gói `TSStudioAndroid-signing-kit.zip` giao kèm APK chứa khóa của bản cài thử và nội dung secret để giữ chữ ký nhất quán; lưu riêng gói này.

## Bố cục source

- `app/src/main/python/township_core.py`: engine gốc, không thay thuật toán.
- `desktop_logic.py`: các hàm editor không phụ thuộc Qt trích từ v1.39.
- `android_engine.py`: phiên làm việc, root, backup, transaction và JSON API.
- `MainActivity.java`: Android host, SAF, luồng nền, WebView chỉ cho phép assets nội bộ.
- `app/src/main/assets`: giao diện responsive và bảng dịch.
- `tools/extract_engine.py`: tái trích xuất core/pure functions từ file Python gốc.
- `tests`: kiểm tra codec, editor, identity, rollback với fixture; không dùng thiết bị thật.

Không upload save riêng, token hay master key vào issue hoặc repository công khai.
