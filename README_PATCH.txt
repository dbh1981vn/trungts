TS Studio Android — Patch tăng tốc và tinh gọn nút thao tác

Áp dụng
1. Tải file ZIP patch và giải nén vào thư mục gốc repository TSStudioAndroid hiện có.
2. Cho phép ghi đè các file cùng đường dẫn.
3. Commit và push lên nhánh main trên GitHub.
4. Mở Actions, chờ workflow Build TS Studio APK hoàn tất.
5. Tải artifact TS-Studio-2.0-Android và cài APK trên thiết bị/giả lập đã root.

Thay đổi trong patch
- Đọc mGameInfo.xml và LocalInfo.xml chung trong một root-shell, có kiểm tra kích thước và độ dài dữ liệu.
- Gộp stage, readback, ghi, sync, xác minh và dọn file tạm để giảm số lần khởi chạy root-shell.
- Giữ backup, kiểm tra save không đổi từ lúc Connect, xác minh sau ghi và rollback khi ghi lỗi.
- Tái sử dụng metadata LocalInfo khi dựng trạng thái giao diện; tránh phân tích lại danh sách friend sau mỗi thao tác.
- Đổi nút trên thẻ tính năng từ Open thành Apply; nút ghi vào file game hiển thị Write to game.
- Land, Museum, All Card, My Card và Golden Pass áp dụng ngay vào bản XML đang chỉnh sửa, không mở popup xác nhận.
- Giữ các tính năng Android có sẵn trong patch trước, gồm Profile Cache, phân nhóm Friend và catalog XML bổ sung.

Các mục Apply vẫn chỉ sửa bản nháp trong ứng dụng. Nhấn Write to game để sao lưu và ghi hai file vào Township.

Đã chạy: 27 kiểm thử Python và kiểm tra cú pháp JavaScript/Python.
Kiểm thử giao diện Playwright chưa chạy trong môi trường đóng gói này vì chưa có Playwright/browser.
APK chưa được build tại đây; GitHub Actions sẽ build APK sau khi bạn push patch.
