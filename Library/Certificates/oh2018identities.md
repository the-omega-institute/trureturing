---
bibkey: oh2018identities
authors: Se-jin Oh, Travis Scrimshaw
year: 2018
title: "Identities from representation theory"
doi: 10.48550/arXiv.1805.00113
url: https://arxiv.org/abs/1805.00113v1
claim: "The paper derives determinant and Pfaffian identities from representation theory and, in an appendix on other q-determinants, conjectures on numerical evidence that the two-shifted Hankel determinants of Cigler's q-Motzkin numbers factor as q^(c_n) f_n(q) for an explicit f_n."
strata_touched:
  - D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation
license: citation-only
triage: anchor
---

# Identities from representation theory

The appendix "Other q-determinants" of Oh and Scrimshaw considers the
`q`-Motzkin numbers defined by Cigler,

> M̃†_{n+1}(q) = M̃†_n(q) + Σ_{k=0}^{n−1} q^{k+1} M̃†_k(q) M̃†_{n−k−1}(q),
> M̃†_0(q) = 1,

recalls Cigler's evaluations of the unshifted and one-shifted Hankel
determinants, and states, "based on numerical computations", the conjecture
labelled `conj:factored_motzkin_2shifted`:

> Define f_n(q) := Σ_{1 ≤ k ≤ n, k ≢ 1 mod 3} q^k if n ≡ 0 mod 3, and
> (q+1)(Σ_{k=0}^{⌊n/3⌋} q^{3k}) otherwise. Then we have
> (det[M̃†_{i+j+2}(q)]_{i,j=0}^{n−1})_{n=1}^∞ = (q^{c_n} f_n(q))_{n=1}^∞
> for some c_n ∈ ℤ_{≥0}.

The same label is used again in the source file for a second conjecture on
the three-shifted determinants, followed by a positivity conjecture
`conj:factored_motzkin_positive` for all even shifts. At `q = 1` the numbers
`M̃†_n(1)` are the Motzkin numbers `1, 1, 2, 4, 9, 21, 51, …`, since both
satisfy the first-return recursion.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1805.00113
- URL: https://arxiv.org/abs/1805.00113v1
- Version and location: arXiv:1805.00113v1 (2018-04-30), source file `q_analogs_repr_theory.tex`, section "Other $q$-determinants" of the appendix: the definition of Cigler's `q`-Motzkin numbers and the first conjecture labelled `conj:factored_motzkin_2shifted`. The journal version, Discrete Math. 342(9) (2019) 2493–2541, DOI 10.1016/j.disc.2019.05.020, was not read.
