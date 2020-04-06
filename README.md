# arccstr

[![Crates.io](https://img.shields.io/crates/v/arccstr.svg)](https://crates.io/crates/arccstr)
[![Documentation](https://docs.rs/arccstr/badge.svg)](https://docs.rs/arccstr/)
[![Build Status](https://travis-ci.org/jonhoo/arccstr.svg?branch=master)](https://travis-ci.org/jonhoo/arccstr)

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
// ArcCStr:
//  + can be created at runtime
//  + can be shared between threads
//  - space overhead is 2*usize (pointer + strong count)
//  - cannot contain internal \0 bytes
use arccstr::ArcCStr;
let s = ArcCStr::try_from("foobar").unwrap();
```

See the [`ArcCStr`][arc] documentation for more details.

Note that this crate requires a nightly build of the compiler as it plays a lot of memory
tricks.

[arc]: struct.ArcCStr.html
