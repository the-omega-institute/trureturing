---
bibkey: flm1988monster
authors: Igor B. Frenkel, James Lepowsky, and Arne Meurman
year: 1988
title: Vertex Operator Algebras and the Monster
doi: 10.1016/S0079-8169(08)X6136-7
claim: Construction and theory of the Monster vertex operator algebra; not a proof of this repository's determinant interface.
strata_touched: []
license: citation-only
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/flm1988monster -->

# Monster vertex operator algebra

Frenkel, Lepowsky, and Meurman construct the Monster module used in
monstrous moonshine. Borcherds's 1992 introduction explicitly identifies
their graded Monster representation as the input to his proof. This book
does not by itself identify a formal determinant with the bivariate
denominator in the repository's Lean carrier.

A chiral VOA construction does not by itself supply a full CFT, a string
model, or a holographic dual. The separate holographic scopes are described
in the [Maldacena note](../Quantum/maldacena1998ads.md) and the
[JLMS note](../Quantum/jlms2016relativeentropy.md).

## Verified locator

- Book title, year, and DOI: https://doi.org/10.1016/S0079-8169(08)X6136-7
- Borcherds 1992, introduction, names the FLM representation:
  https://math.berkeley.edu/~reb/papers/monster/monster.tex

The bibliographic identity and Borcherds's attribution were checked; the
FLM book's full text was not inspected.

## Untwisted lattice input (Bakalov–Kac)

The untwisted lattice input used before the reflection-twisted Monster
extension is the construction in BK2004v1: Bojko Bakalov and Victor G. Kac,
[*Twisted Modules over Lattice Vertex Algebras*](https://arxiv.org/abs/math/0402315v1), §4.1.
The cited section is on printed pp. 8–9 of arXiv v1 (2004-02-19).
For an integral lattice $Q$, that section forms
$V_Q=S\otimes\mathbb C_\varepsilon[Q]$, with the twisted group-algebra multiplication and
charge shift in (4.3) and (4.6), then defines the exponential generating field
in (4.12) and the ordered two-field product in (4.14) used for locality.
Theorem 4.1 states the resulting lattice vertex-algebra structure. The paper
allows odd integral lattices with parity; for an even lattice that parity is
zero, which is the prospective ordinary lattice scope here.

This source supports the untwisted lattice construction used before the
reflection-twisted Monster extension; it is not itself a complete Monster,
full-CFT, string, or AdS/CFT result. The existing
[`PolynomialFockChargedStateField.chargedY`](https://github.com/the-omega-institute/trureturing/blob/24096e7dc967100a29810cc7db1aa7748efa871d/D5/S3/VertexAlgebra/PolynomialFockChargedStateField.lean)
stays on a fixed polynomial Fock carrier and is not the displayed
charge-changing direct-sum field. BK2004v1 is the inspected arXiv v1 source;
Crossref independently matches its authors and title to the chapter in *Lie
Theory and Its Applications in Physics V* (2004), pp. 3–26,
[DOI 10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001).
The equation and theorem numbers below refer to arXiv v1, not to an inspected
published chapter. These literature references do not establish a Lean
realization of the charge-changing lattice fields.

- **§4.1, (4.3) and (4.6):** $e_\alpha e_\beta=\varepsilon(\alpha,\beta)e_{\alpha+\beta}$ and $e_\gamma(s\otimes e_\alpha)=\varepsilon(\gamma,\alpha)s\otimes e_{\alpha+\gamma}$, respectively.
- **§4.1, (4.12) and (4.14):** the exponential field $Y_\alpha(z)$ and the ordered product $Y_\alpha(z)Y_\beta(w)$ underlying mutual locality.
- **§4.1, Theorem 4.1:** the fields $h(z)$ and $Y_\alpha(z)$ generate the vertex-algebra structure on $V_Q$, with the displayed translation and conformal data in (4.15)–(4.16).
