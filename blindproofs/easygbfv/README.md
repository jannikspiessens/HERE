# easyGBFV

An easy-to-use GBFV library based on [fheanor](https://github.com/FeanorTheElf/fheanor).

Run the example found in `examples/basics.rs` using
```
cargo run -r --example basics
```
For optimal performance, one should enable the `mpir` feature flag for the `feanor-math` crate and the `hexl` feature flag for the `fheanor` crate (see `Cargo.toml`). This requires installing the [hexl](https://github.com/IntelLabs/hexl) and [mpir](https://github.com/wbhart/mpir) libraries respectively.

## Dependencies

This library depends on
    - a fork of the fheanor crate
    - the `matmul` module in the proofs crate

## Disclaimer

This is a first working version. Performance updates to come.

