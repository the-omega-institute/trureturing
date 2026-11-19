---
bibkey: bakalovkac2004lattice
authors: Bojko Bakalov and Victor G. Kac
year: 2004
title: Twisted Modules over Lattice Vertex Algebras
doi: 10.1142/9789812702562_0001
url: https://arxiv.org/abs/math/0402315v1
claim: In arXiv v1, §4.1 gives the lattice generating fields and conformal vector, and §4.2 equation (4.23) gives the fractional Heisenberg bracket.
strata_touched: []
license: citation-only
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/bakalovkac2004lattice -->

# Lattice generating fields and conformal data

Section 4.1, printed pages 8–9 of arXiv math/0402315v1, constructs
the lattice carrier as the oscillator symmetric algebra tensored with the
twisted group algebra of all integral charges. Equations (4.12)–(4.14)
give the charged generating field and ordered product. Equation (4.15)
specifies translation through its neutral-current commutator and charged
ground-state action; (4.16) gives the inverse-form quadratic conformal
vector. Theorem 4.1 supplies the surrounding lattice vertex-algebra result.
The repository's actual matrix Sugawara component verifies the mode laws
on its existing even-lattice carrier; it does not assert the full all-state
vertex-algebra theorem, positivity, or finite-dimensional grading.

The source identification and equation locators are recorded in the
existing untwisted lattice input section of
[the FLM background note](flm1988monster.md). Equation numbers refer to
arXiv v1, rather than the published chapter. The rank-one Lean proof
architecture adapted for the matrix commutator calculation is separately
attributed to [Kytölä's pinned source](kytola2025virasoro.md).

## Twisted current formulas

Section 4.2, printed page 10, equation (4.23) gives
$[h^M_{(m)},(h')^M_{(n)}]=(\pi_{Nm}h\mid h')m\delta_{m,-n}$.
For the order-two sign involution, the projection is the identity on
the sign-odd currents for $m\in\mathbb Z+\tfrac12$. Section 3.2,
equation (3.12), gives the twisted field commutator. For the invariant
lattice conformal vector of (4.16), its products with the weight-one
current state give the mode law $[L_j,h_{(m)}]=-m h_{(j+m)}$.

## Verified locator

- Primary version: https://arxiv.org/abs/math/0402315v1, §4.1,
  equations (4.12)–(4.16), Theorem 4.1, §4.2 equation (4.23), and §3.2
  equation (3.12).
- Published bibliographic identity: https://doi.org/10.1142/9789812702562_0001.
