---
bibkey: mathlib2026starsbars
authors: Yaël Dillies, Bhavik Mehta, Huỳnh Trần Khanh, Stuart Presnell and Mathlib contributors
year: 2026
title: Mathlib.Data.Sym.Card — Stars and bars
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Sym/Card.lean
claim: Multisets of size t on an alphabet of size d, equivalently weak compositions of t into d ordered parts, number choose(d+t-1,t); for d>0 this equals choose(t+d-1,d-1).
strata_touched:
  - D5/S3/TotalVariation/ParityKernelMasses
  - D5/S3/TotalVariation/TreeParityKernel
license: Apache-2.0
triage: anchor
---

# Stars and bars for composition masses

The source title is the `Stars and bars` module documentation in
`Mathlib/Data/Sym/Card.lean` at the immutable Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. The bibliographic year identifies
the consulted library version, rather than the origin of this classical count.
The source is released under Apache-2.0 and credits the authors above.

`Sym.card_sym_eq_choose` states that, for a finite alphabet `A`,

$$
\left|\operatorname{Sym}(A,t)\right|
=\binom{|A|+t-1}{t}.
$$

The module's informal statement explicitly identifies these multisets with
nonnegative ordered tuples whose sum is `t`. The equivalence
`Sym.equivNatSumOfFintype` in the same revision's
`Mathlib/Data/Finsupp/Multiset.lean` realizes this identification. Taking `A = Fin d`
and applying `Nat.choose_symm` gives, for `d > 0`,

$$
\#\{r\in\mathbb N^d:\textstyle\sum_i r_i=t\}
=\binom{t+d-1}{d-1}.
$$

The locator and statement are checked against the immutable upstream source
and the repository's pinned local copies of `Data/Sym/Card.lean`,
`Data/Finsupp/Multiset.lean` and `Data/Nat/Choose/Basic.lean`.

This source supplies the ordinary weak-composition count used to normalize
composition parity masses. The prescribed-parity map `r_i = 2t_i + x_i`,
its legal-support conditions and the ordered-tree gap equivalence are
separate constructions; they are not statements of `Sym.card_sym_eq_choose`.
