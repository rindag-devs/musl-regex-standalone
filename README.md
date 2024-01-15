# musl regex.h standalone

This project is an extraction of the regex library in musl libc. It separates the regular expression POSIX API part of musl libc into a header-only library which does not contain any dependencies except the ANSI C standard library.

If the C standard library you use does not provide `regex.h`, or the provided `regex.h` is damaged, you can put `regex.h` in the project into the system include folder or replace the damaged `regex.h`.

This project was tested in the following environment:

- gcc 12.3.0, openSUSE Linux, x86_64
- clang 16.0.6, openSUSE Linux, x86_64
- MSVC cl.exe 19.38.33134, Windows 11, x86_64
- MSYS2 ucrt64 gcc 13.2.0 , Windows 11, x86_64

## License

Keep original [MIT License](https://git.etalabs.net/cgit/musl/tree/COPYRIGHT) of musl project.
