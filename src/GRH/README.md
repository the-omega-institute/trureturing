# Dirichlet L-functions and the Riemann hypothesis

The `GRH` Lake target ports the compact edition of Levent Alpöge's proof. Its
modules preserve the upstream statements and proof bodies under
`GRH` and use the pinned official Mathlib backend.
[`lsernau/grh-lean` at `72fead102f663d5c7a407964a13dc0cf9d977207`](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact)

Build the proof with `make lean LEAN_TARGETS=GRH`.
Consumers use `import GRH` and can apply the five
upstream declarations directly. All five depend on `propext`, `Classical.choice`
and `Quot.sound`.

- `riemannHypothesis` has Mathlib's type `RiemannHypothesis`.
- `riemannZeta_eq_zero_re` places every zero of the Riemann zeta function other
  than the negative even integers on the critical line, with the pole excluded.
- `LFunction_ne_zero_of_half_lt_re` gives nonvanishing for `1 / 2 < s.re`,
  with `s = 1` excluded for the principal character.
- `LFunction_eq_zero_re` gives `s.re = 1 / 2` for zeros with `0 < s.re < 1`
  for every character of every positive modulus.
- `LFunction_eq_zero_re_of_isPrimitive` gives the primitive-character case.

The port can be retired once pinned Mathlib has equivalent proofs of these
conclusions and each project consumer has switched to them.

[Apache 2.0 license](../../docs/reports/third-party/grh-lean/LICENSE.txt) ·
[Notice](../../docs/reports/third-party/grh-lean/NOTICE.txt) ·
[Attribution](ATTRIBUTION.md) ·
[References](REFERENCES.md)
