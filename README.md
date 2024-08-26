# Analyzer for Timed Automata

This project provides an analyzer for Timed Automata.
In order to build this project to WebAssembly, you need to install _wasm-pack_.
Assuming you have already installed Rust, you can simply run `cargo install wasm-pack`.
For further information on compiling Rust to WebAssembly, we refer to the [MDN Web Docs](https://developer.mozilla.org/en-US/docs/WebAssembly/Rust_to_Wasm).

## Building the WebAssembly Binary

_wasm-pack_ offers a simple solution to generate a package for NPM, just run the following command:

```sh
wasm-pack build --target bundler
```

## Linting

This project uses Clippy for linting.
For instructions on how to install Clippy, see the [Clippy repository](https://github.com/rust-lang/rust-clippy).
To run Clippy, simply execute `cargo clippy`.
