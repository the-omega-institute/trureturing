---
bibkey: gonzalez2026equivalence
authors: B. J. González and E. R. Negrín
year: 2026
title: A new equivalence to the Riemann Hypothesis by means of the Salem integral equation
doi: null
url: https://arxiv.org/abs/2604.15396v1
claim: The positive-scale eta Mellin identity and the power-function Salem criterion, with the source-to-formalization correspondence and endpoint exclusions specified below.
strata_touched:
  - D5/S3/Weil/ZetaBridge/FermiMellin
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Weil/gonzalez2026equivalence -->
# Fermi Mellin and Power-Function Salem Statements

## Verified locator

https://arxiv.org/abs/2604.15396v1

The source is the two-page v1 preprint linked above (E03 in the RH source
atlas). Physical and printed page numbers agree. Its official PDF is
https://arxiv.org/pdf/2604.15396v1, SHA256
`9430f878e722af1b6b568459a7c540d6ca353a3c482623da86672df877bd73c2`.
This is a preprint statement attribution, not a trusted Lean axiom or an
assertion of peer review. The repository proofs carry the formal claims.

The paper explicitly calls its function written **xi** the Riemann
zeta-function and gives its ordinary Dirichlet series on page 1.
Its xi therefore corresponds to `riemannZeta`, **not** to `xiReading` or
the completed Riemann xi-function. Its eta is the Dirichlet eta-function.

## Mellin identity and domain correspondence

Page 2, equation (1), states, for complex s with Re(s) > 0 and every real
x > 0,

\[
I_x(s):=\int_0^\infty\frac{t^{s-1}}{e^{xt}+1}\,dt
=x^{-s}\Gamma(s)\eta(s).
\]

The printed right side uses eta. The preceding eta series is stated for
Re(s) > 0; the separate relation eta(s) = (1 - 2^(1-s)) xi(s) is introduced
for Re(s) > 1, followed by the sentence that it extends xi to
0 < Re(s) < 1. Those distinct source clauses must not be presented as a
single verbatim full-half-plane zeta-product display.

For t > 0 the complex power uses the real logarithm, so its norm is
t^(Re(s)-1). With sigma = Re(s) > 0, the norm of the kernel is bounded by
t^(sigma-1) near zero and by t^(sigma-1) exp(-xt) at infinity. This explains
the absolute-convergence/complex `IntegrableOn` reading of (1), including
s = 1. Positive scaling u = xt yields I_x(s) = x^(-s) I_1(s), with the
same exponent and the same denominator exp(xt) + 1; there is no shift or
extra Gamma normalization.

The off-one formal statement is the classical zeta-product form of this
identity. For comparison, [DLMF 25.5.3](https://dlmf.nist.gov/25.5#E3)
prints

\[
\zeta(s)=\frac{I_1(s)}{(1-2^{1-s})\Gamma(s)},\qquad \Re(s)>0,
\]

under the standing subsection clause **s != 1**. Its displayed variable
x is an integration variable, not an arbitrary scale parameter. DLMF's
quotient must not be read as Lean's totalized division at a zero of the
dyadic factor. Away from such zeros, multiplication gives the product
identity; at nonreal dyadic zeros on Re(s) = 1, continuity of the Mellin
integral and of the product extends that identity. Equivalently the
classical eta factorization extends analytically across this line away
from the zeta pole. These are the normal-form/continuation steps relating
the classical identity to `fermi_mellin_eq_of_ne_one`, not additional
printed clauses attributed to E03. They retain **all** Re(s) > 0, s != 1,
including Re(s) = 1 with s != 1, without dividing by the dyadic factor.

[DLMF 25.12.14](https://dlmf.nist.gov/25.12#E14) instead defines
F_a(y) = Gamma(a+1)^(-1) times the integral of t^a/(exp(t-y)+1).
Its printed condition is a > -1 (the symbol metadata calls a complex);
y is a real **shift**. Matching the scale-one kernel requires y = 0,
a = s-1 and multiplication by Gamma(s). It is not a literal citation for
the arbitrary positive multiplier x or the full complex domain here.
Neither this passage nor DLMF 25.5.3 supplies the explicit endpoint or
punctured product limit below. The DLMF annotations' underlying books
and articles are not separately claimed as inspected sources.

## Salem correspondence and quantifiers

Page 1 and the proof on page 2 assert RH iff, for **each** real
1/2 < delta < 1, there is **no real gamma** for which f(t) = t^(i gamma)
solves

\[
\int_0^\infty\frac{t^{\delta-1}}{e^{xt}+1}f(t)\,dt=0
\quad\text{for every real }x>0.
\]

The intermediate zero equivalence on page 2 uses the larger strip
0 < delta < 1 and every real gamma, with s = delta + i gamma.
For t > 0, t^(delta-1) t^(i gamma) = t^(s-1), exactly the formal kernel.
Gamma(s) has no zero on this strip, and 1 - 2^(1-s) cannot vanish there
because its vanishing forces Re(s) = 1. Also x^(-s) is nonzero for x > 0.
Thus I_1(s) = 0 iff I_x(s) = 0 for every x > 0, and each is equivalent
to zeta(s) = 0. Negating gives the formal scale-one pointwise nonvanishing
equivalence. Quantifying delta and gamma gives the formal RH criterion:
the source's negated all-scale solution condition is equivalent to
nonvanishing at scale one, not merely implied by it. The repository's
frozen right-half-strip reduction connects the source's critical-strip
RH wording to the standard Lean `RiemannHypothesis`.

The bounded-measurable uniqueness result quoted as Salem (1953) on page 1
is a different statement. This note attributes the explicit power-function
criterion to the inspected preprint; it does not claim to have inspected
Salem's original publication or to formalize general bounded-measurable
uniqueness (A069).

## Per-declaration assessment

All names below belong to `D5/S3/Weil/ZetaBridge/FermiMellin`.

| Declaration | Provenance | Exact correspondence or retained repository contribution |
| --- | --- | --- |
| `fermi_mellin_integrable` | literature-attested | The convergence domain of Eq. (1): every real x > 0 and complex Re(s) > 0, including s = 1; absolute integrability is explained above. |
| `fermi_mellin_eq_of_ne_one` | literature-attested | Classical zeta-product form of Eq. (1), with the eta factorization, positive scaling and off-pole continuation spelled out above; DLMF 25.5.3 corroborates the off-one domain. It is not a verbatim E03 zeta-product display. |
| `fermi_mellin_product_tendsto_one` | repo-derived | Punctured complex limit of the product to log(2)/x for every x > 0, proved from the zeta residue and the dyadic derivative. Neither inspected source states this limit. |
| `fermi_mellin_at_one` | repo-derived | Actual integral equals log(2)/x for every x > 0. E03 includes s = 1 in the eta-form domain but prints no log(2) evaluation; the repository identifies the integral by continuity and the punctured limit. |
| `fermi_mellin_identity` | repo-derived | Conjunction of integrability with an explicit if-s-equals-one endpoint branch and the off-one product. This totalized Lean packaging and its proved endpoint are not printed in E03. |
| `fermi_mellin_nonzero_iff_zeta_nonzero` | literature-attested | Page 2 zero equivalence, restricted to 1/2 < Re(s) < 1 and expressed at scale one, with zero/nonzero complementation and positive-scale equivalence justified above. |
| `salem_mellin_nonvanishing_iff_rh` | literature-attested | Pages 1–2 power-function criterion, preserving every delta and gamma, converted equivalently from the all-positive-scale zero equation to scale-one nonvanishing. |

The three repository-derived labels make no mathematical novelty claim.
The preprint has no explicit s = 1/log(2)/punctured-limit statement.
Statement provenance is separate from implementation authorship: the
modified dbsanfte/RiemannGaussian proof slice remains acknowledged in
[its source and license note](sanftenberg2026fermi.md), with its original
scope and copyright intact.
