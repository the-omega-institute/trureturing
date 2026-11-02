---
bibkey: mathlib2026etacusps
authors: "The Mathlib Community; Daniel M. Kane (application context)"
year: 2026
title: "Pinned eta and discriminant suppliers for constant cusp multipliers"
doi: null
url: https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/ModularForms
claim: "Classical eta nonvanishing, inversion and discriminant modularity supply a constant unit cusp multiplier and exact third-cusp phases."
strata_touched:
  - D5/S3/Arith/ModularForms/EtaCuspMultiplier
  - D5/S3/Arith/ModularForms/EtaCuspTransform
  - D5/S3/Arith/ModularForms/EtaThirdCusp
  - D5/S3/Arith/ModularForms/EtaCuspPhases
  - D5/S3/Arith/ModularForms/EtaKaneCusp
license: citation-only
triage: anchor
---

# Constant eta multipliers and the third-cusp phase

The formal suppliers use Lean v4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
`ModularForm.eta_ne_zero` and
`ModularForm.eta_comp_eq_csqrt_I_inv` in `DedekindEta.lean` provide
nonvanishing and inversion on the upper half-plane. `CuspForm.discriminant`
in `Discriminant.lean`, via `SlashInvariantForm.slash_action_eqn''`, provides
its transformation for every integral determinant-one matrix. The
underlying discriminant is eta to the twenty-fourth power.

For a matrix with positive lower-left entry, the ratio
`eta(gamma*tau)/(sqrt(c*tau+d)*eta(tau))` is continuous and its twenty-fourth
power is one. Connectedness of the entire upper half-plane and discreteness
of the finite set of roots make the ratio a single constant, independent of
tau. This proves an unspecified unit multiplier. It does not identify that
constant with a general Dedekind-sum formula.

Here E(q) is the Euler product and P(q)=1/E(q) is the reciprocal partition
product. The shift is explicit: P(exp(2*pi*i*tau)) equals
exp(pi*i*tau/12)/eta(tau). The cusp theorems retain this shift and quantify
over every complex w with positive real part, with principal square roots.
Translation by three follows from the eta product; the matrix ST^3S fixes
the exact multiplier by evaluation at i, then constancy extends it to the
entire upper half-plane. The partition phase at 1/3 is exp(pi*i/18), and
conjugation gives exp(-pi*i/18) at 2/3. Inversion fixes the denominator-one
phase as one. The resulting H(q)=E(q)^2/E(q^3) phase is exp(-pi*i/9) at 1/3,
with its conjugate at 2/3. Their negative Fourier-extraction weights yield
2*cos(2*pi*n/3+pi/9).

The application is Daniel M. Kane, *Resolution of a conjecture of Andrews
and Lewis involving cranks of partitions*,
https://cseweb.ucsd.edu/~dakane/AndrewsConjecture.pdf, especially the local
circle-method transformations. Kane owns the H sign theorem and circle
method. The constant-multiplier reduction is a formal realization of
classical modular infrastructure; no new sign theorem, priority, uniqueness
or external open-problem resolution is asserted here.

The broader target is Bringmann--Han--Heim--Kane arXiv:2409.07164v1,
Appendix A Table 1, the denominator-ten row (primary extraction lines
1650--1651): E(q)^9/E(q^3)^10, all unshifted coefficients including index zero.
Its required period-nine signs are +-+--+--+. General cubic lifting is already
in arXiv:2507.16644v1 Lemma 9 and main theorem part 2(9). These component
sources do not formalize Farey arcs, Hankel integrals, explicit circle errors,
coefficient signs, finite exceptions, smoothing, or the complete target.
