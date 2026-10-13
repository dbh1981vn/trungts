Bản vá mở rộng catalog XML cho project TS Studio Android.

Giải nén vào thư mục gốc repository Android và cho phép ghi đè file cùng đường dẫn. Sau đó commit/push lên GitHub và chạy workflow Build TS Studio APK.

Nội dung chính:
- 19 Skin ID bổ sung từ skins.xml; tên bị cắt cụt và mục Default được bỏ qua.
- 24 ID Profile bổ sung từ DataVarCatalog.
- 29 Decoration ID và 40 cấu trúc FragmentedBeauty bổ sung từ XML; 2 city sign bổ sung từ BuildingsStash. Không đưa LandscapesIcon/dalesIcon/roadsIcon vì đây là marker giao diện.
- Giữ thay đổi Set Selected Decoration tối đa 100.
- Bổ sung kiểm thử regression và cập nhật tools/extract_engine.py để lần trích xuất tiếp theo giữ lại các catalog này.

Các thay đổi áp dụng cho mã nguồn Android. Không sửa chương trình Python desktop gốc và không thay đổi trực tiếp file save XML của thành phố.
