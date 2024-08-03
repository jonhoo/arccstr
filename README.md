[![Crates.io](https://img.shields.io/crates/v/arccstr.svg)](https://crates.io/crates/arccstr)
[![Documentation](https://docs.rs/arccstr/badge.svg)](https://docs.rs/arccstr/)
[![Codecov](https://codecov.io/github/jonhoo/arccstr/coverage.svg?branch=main)](https://codecov.io/gh/jonhoo/arccstr)

Thread-safe reference-counted null-terminated strings.

This crate provides a space efficient mechanism for storing immutable strings.
The best illustration of this is to go over the alternatives:

```rust
// &str:
//  - content must be known at compile time
//  + can be shared between threads
//  + space overhead is 2*usize (fat pointer to the string)
let s = "foobar";
// String
//  + can be created at runtime
//  - cannot be shared between threads (except with Clone)
//  - space overhead of 3*usize (Vec capacity and len + pointer to bytes)
//  - accessing string requires two pointer derefs
let s = format!("foobar");
// CString:
//  * mostly same as String
//  * space overhead is 2*usize (uses Box<[u8]> internally)
//  - cannot contain internal \0 bytes
use std::ffi::CString;
let s = CString::new("foobar").unwrap();
// CStr:
//  + space overhead is just the pointer (1*usize)
//  - hard to construct
//  - cannot contain internal \0 bytes
//  - generally cannot be shared between threds (lifetime usually not 'static)
use std::ffi::CStr;
let s: &CStr = &*s;
// Arc<String>:
//  + can be created at runtime
//  + can be shared between threads
//  - space overhead is 7*usize:
//     - pointer to Arc
//     - weak count
//     - strong count
//     - pointer to String
//     - String overhead (3*usize)
use std::sync::Arc;
let s = ArcCStr::try_from(format!("foobar")).unwrap();
// Arc<str>:
//  + can be created at runtime
//  + can be shared between threads
//  - space overhead is 4*usize:
//     - pointer to Arc
//     - str length
//     - weak count
//     - strong count
let s: Arc<str> = Arc::from("foobar");
// Arc<CStr>:
//  + can be created at runtime
//  + can be shared between threads
//  - space overhead is 4*usize:
//     - pointer to Arc
//     - CStr length
//     - weak count
//     - strong count
//  - cannot contain internal \0 bytes
let s: Arc<CStr> = Arc::from(CStr::from_bytes_with_nul(b"foobar\0").unwrap());
// ArcCStr:
//  + can be created at runtime
//  + can be shared between threads
//  - space overhead is 2*usize (pointer + strong count)
//  - cannot contain internal \0 bytes
use arccstr::ArcCStr;
let s = ArcCStr::try_from("foobar").unwrap();
```

See the [`ArcCStr`][arc] documentation for more details.

[arc]: struct.ArcCStr.html
