---
bibkey: mian2026erdos7kernel
authors: "Ibrahim Mian; Shayaan Siddique"
year: 2026
title: "Kernel-Checked Exclusions for the Erdős--Selfridge Odd Covering Problem: Any Odd Covering of ℤ Has lcm Exceeding 10000"
doi: null
url: https://arxiv.org/abs/2607.25628
claim: "A Lean 4 development proves that any finite covering of ℤ by distinct odd moduli greater than one has lcm exceeding 10000; the unrestricted Erdős--Selfridge problem remains open."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: "Paper: arXiv source; implementation: Apache 2.0"
triage: anchor
---

# A kernel-checked finite exclusion

The inspected primary source is [arXiv:2607.25628](https://arxiv.org/abs/2607.25628),
submitted 28 July 2026. Its headline theorem is
`odd_covering_lcm_gt_10000`: for a finite family of congruence classes with
moduli greater than one, odd, and injective as numerical moduli, a cover of
`ℤ` has

\[
  10000 < \operatorname{lcm}_i n_i.
\]

The proof is a Lean-kernel development published at
[`ibrahimmian36/centurion`](https://github.com/ibrahimmian36/centurion), whose
main revision inspected here is `76ed2325673ade215d8ce56e2c6d66bffd6d0ed4`.
It combines the density/abundancy reduction, a kernel enumeration of the odd
non-deficient candidates below `10000`, and per-candidate CRT capacity
certificates. The source reports the standard three-axiom foundation and no
`sorry` or `native_decide` in its published development.

This is an external reusable finite exclusion, not a settlement of the
unrestricted problem. It rules out every hypothetical odd cover whose lcm is
at most `10000`; it says nothing about arbitrarily large lcm or about the
phase-preserving global repair still open in the present Erdős #7 lane. The
current repository records the theorem and source identity but does not claim
to have replayed that external Lean build locally. Reusing it therefore avoids
duplicating the published finite computation while keeping its verification
boundary explicit.
