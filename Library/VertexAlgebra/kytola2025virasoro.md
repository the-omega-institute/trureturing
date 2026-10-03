---
bibkey: kytola2025virasoro
authors: Kalle Kytölä
year: 2025
title: VirasoroProject, Sugawara.lean
doi: null
url: https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean
claim: The pinned Lean source proves the bosonic Sugawara commutators from Heisenberg relations and local truncation, including the Virasoro central charge one.
strata_touched: []
license: Apache-2.0
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/kytola2025virasoro -->

# Bosonic Sugawara formalization

Kytölä's `Sugawara.lean` defines normal-ordered operators from a locally
truncated Heisenberg action. It states both the current commutator
`[L_n,J_m]=-mJ_{n+m}` and the full Virasoro commutator with central charge
one. These general statements do not themselves construct the concrete
polynomial Fock modes used in problem 2145.1.

The fixed revision uses Lean 4.34.0 and Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`; this repository uses
Lean 4.33.0 and Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. The source is an
original-proof transplant, not a compiled dependency of this repository.

## Source ownership and adaptation

`PolynomialFockVirasoroCentral.L_commutator` adapts Kalle Kytölä's
original proof at this immutable revision. The central calculation is
`Sugawara.lean` lines 361–571; the normal-ordering boundary and pointwise
finite-sum transport use the preceding definitions and proof steps in
lines 70–292. The integer interval sums are from
`CentralChargeCalc.lean` lines 35–76. Scalar and commutator normalization
is inlined; the upstream Lie-algebra and representation packaging in
lines 573–724 is not included. The generic locally truncated Heisenberg
premises are replaced by the frozen concrete polynomial Fock support,
Heisenberg and Sugawara-current declarations. The all-integer conclusion
uses the existing `PolynomialFockSugawaraSupport.L`, not a new operator.

The upstream headers identify Kalle Kytölä as copyright holder and author,
and license the source under Apache 2.0. The repository root `LICENSE`
contains the complete Apache 2.0 terms of the upstream `LICENSE`; the only
textual difference is the appendix's example copyright line, which names
The Omega Institute instead of the upstream fill-in placeholders. The
immutable upstream tree contains `LICENSE` and no `NOTICE`. The modified Lean source preserves the
copyright, source revision and a modification notice. Its proof lineage
is literature-attested; it is not an independently authored Sugawara proof.

The transplant is retired only when this repository's own pinned Mathlib
contains an equivalent result and direct application to these actual
Fock operators compiles. Upstream publication or acceptance alone is not
a retirement condition. The current scope is the rank-one conformal
operator relation at central charge one; no VOA, Monster module,
central-charge-24 realization, fusion or OPE is supplied.

## Verified locator

- Commit `5ff4245383b2cdd4eea7a0524bc1274c32041eb4`,
  `VirasoroProject/Sugawara.lean`, opening documentation and named main
  statements; source and project pins checked on 29 September 2026:
  https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean
