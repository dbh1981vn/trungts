# Phạm vi kiểm chứng

- 21 unit test đạt: codec XML, cổng Connect/revision, sửa level đồng bộ hai file, editor theo mục được chọn, Golden Pass giữ thuộc tính chưa biết khi sửa/xóa reward, Train theo toa, Clone V3 giữ identity, backup/restore, từ chối ZIP traversal, bắt buộc Send Cards key, phát hiện save đổi sau Connect và rollback khi ghi lỗi giữa chừng.
- Giao diện được chạy bằng Chromium với cầu Android mô phỏng: mọi editor mở được, bố cục vừa màn hình rộng 393 px, banner chào mừng đã được gỡ, payload chỉnh toa tàu đúng, không có lỗi JavaScript. Đây không phải kiểm tra WebView trên Android thật.
- Chưa kiểm chứng trên điện thoại root hoặc Township đang chạy. Các thao tác server (Send Cards/FetchCity), Auto LV3 và việc game chấp nhận các giá trị cần kiểm tra trên thiết bị/tài khoản của người dùng.
- Bản chuyển đổi giữ engine XML gốc. Giao diện được viết mới; các khác biệt với desktop được ghi trong README.

Lệnh kiểm tra engine: `python -m unittest discover -s tests -v`.
Kiểm tra UI tùy chọn: cài `playwright`, rồi chạy `python tools/test_ui.py /absolute/path/to/chrome /absolute/path/to/output`.
