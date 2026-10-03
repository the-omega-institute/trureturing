---
bibkey: matsuo1997locality
authors: Atsushi Matsuo; Kiyokazu Nagatomo
year: 1997
title: On axioms for a vertex algebra and locality of quantum fields
doi: null
url: https://arxiv.org/abs/hep-th/9706118v1
claim: Pairwise local creative fields with a common translation operator reconstruct a vertex algebra; residue products preserve locality.
strata_touched: []
license: citation-only
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/matsuo1997locality -->

# Local fields and reconstruction

Proposition 1.5.5, printed page 11, proves locality of residue products of
pairwise local fields. For residue index minus one, the sum of the three
pairwise orders is a sufficient locality order. These orders depend on the
fields, not on the vector to which their modes are applied.

Theorem 5.2.1, printed page 33, includes lower truncation, all-state locality,
creation and a common translation operator annihilating the vacuum among
the reconstruction conditions. Theorem 5.4.1, printed page 35, reconstructs
state fields from creative local generators, their vacuum-mode span and a
common translation operator. Its construction uses divided derivatives
and ordered normal products.

The polynomial Fock construction in `PolynomialFockStateField.lean` uses
the actual current, sorts the monomial occurrences, explicitly right-nests
normal products and extends by the monomial basis. This is an implementation
of classical mathematics, not a claim of a new reconstruction theorem.
The actual `L(-1)` translates every resulting field. The locality proof uses
the finite-support residue boundary and the three-order binomial cancellation
in `FieldNormalProductLocality.lean`; induction through arbitrary words and
finite polynomial supports chooses an order independently of the input vector.
The quadratic conformal state's modes are the existing `L(n-1)`. These field
conditions do not supply a bundled Jacobi-identity interface. The reference does not supply Lean proof
terms, an actual Monster realization or a spacetime reconstruction.

The rational polynomial model embeds through `MvPolynomial.map (algebraMap ℚ ℂ)`.
The map is injective, preserves every variable and the vacuum, and commutes
with polynomial partial derivatives. Thus the rational creation operator
`X_k * p` and annihilation operator `(k+1) • pderiv k p` map to the same
complex operators used by the construction. Slot `k` represents the mode
with creation index `-(k+1)`, not a changed Heisenberg normalization.

## Source adaptation

`FieldNormalProduct.lean` selectively adapts Hasse lifting and the finite
support arguments from Scott Carnahan's `VertexAlg/VertexBasic/VertexOperator.lean`
at revision `4453e34ec390e82a0c789c731ada8f9a6e86bdea` of
`ScottCarnahan/vertexAlg`. The original file's SHA-256 is
`ec4e543a6411876f19638138f825668785f2f30ace3f30cbe9328640ac02a2e2`.
Its copyright header grants Apache-2.0 licensing; that revision's recursive
tree contains no `LICENSE` or `NOTICE` file. This repository's root `LICENSE`
provides the full Apache-2.0 terms. The adapted source preserves the original
copyright and author notice and identifies its modifications.

The source pins Lean 4.33.1 and Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`; this repository instead uses Lean
4.33.0 and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`.
The transplant reuses the latter's `LaurentSeries.hasseDeriv`; it does not
alter either dependency pin. Only the minus-one coefficient construction
is retained, with its bounded-pole argument expressed using finitely many
actual intermediate states. The ordinary covariance calculation is a
separate Lean proof. The derivative and normal-product locality proofs are
also developed here from coefficient functions, not attributed to an upstream
compiled locality theorem.

Upstream derivative-locality and Dong locality statements are commented
sketches, not compiled suppliers. No such sketch is copied as a theorem
or assumed as an axiom. The transplant is retired only when direct use of
equivalent declarations from this repository's own pinned Mathlib compiles
for the actual Fock consumer.

## Verified locator

- Matsuo–Nagatomo, arXiv `hep-th/9706118v1`, PDF SHA-256
  `2e1dabebeffe511c8bd14c0a4e6449afefcf508a02135d96df2042a0ccca07ea`,
  Proposition 1.5.5 and Theorems 5.2.1 and 5.4.1:
  https://arxiv.org/abs/hep-th/9706118v1
- Carnahan source:
  https://github.com/ScottCarnahan/vertexAlg/blob/4453e34ec390e82a0c789c731ada8f9a6e86bdea/VertexAlg/VertexBasic/VertexOperator.lean
