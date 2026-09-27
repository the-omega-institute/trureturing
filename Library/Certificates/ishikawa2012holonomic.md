---
bibkey: ishikawa2012holonomic
authors: Masao Ishikawa, Christoph Koutschan
year: 2012
title: "Zeilberger's Holonomic Ansatz for Pfaffians"
doi: 10.48550/arXiv.1201.5253
url: https://arxiv.org/abs/1201.5253v2
claim: "The paper proves by the holonomic ansatz that Pf((j-i) M_{i+j-3})_{1<=i,j<=2n} equals the product of 4k+1 over k < n for the Motzkin numbers M_n, and conjectures product formulas for the Pfaffians Pf((j-i) M^(k)_{i+j-2}) of the columns of the Motzkin triangle and of sums of two consecutive entries."
strata_touched:
  - D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation
license: citation-only
triage: anchor
---

# Zeilberger's holonomic ansatz for Pfaffians

Ishikawa and Koutschan adapt Zeilberger's holonomic ansatz from determinants
to Pfaffians. For a `2n × 2n` skew-symmetric matrix `A = (a_{i,j})` the section
on Pfaffians defines

> Pf(A) = Σ ε(σ₁, σ₂, …, σ_{2n−1}, σ_{2n}) a_{σ₁σ₂} ⋯ a_{σ_{2n−1}σ_{2n}},

where the summation is over all partitions `{{σ₁,σ₂},…,{σ_{2n−1},σ_{2n}}}`
of `[2n]` into two-element subsets and `ε` is the sign of the permutation
`(1 2 ⋯ 2n ↦ σ₁ σ₂ ⋯ σ_{2n})`. With the Motzkin numbers `M_n`, which count
the paths from `(0,0)` to `(n,0)` with steps `U = (1,1)`, `H = (1,0)`,
`D = (1,−1)` that never run below the horizontal axis, Theorem `thm.pfMotz`
states

> Pf((j−i) M_{i+j−3})_{1≤i,j≤2n} = ∏_{k=0}^{n−1}(4k+1) for all n ≥ 1.

The closing section writes `𝓜^{(k)}_i = h(i,2k−1)` for the number of Motzkin
paths from `(0,0)` to `(i−1,k−1)`, so that `M_n = 𝓜^{(1)}_{n+1}`, and states
Conjecture `conj.gen`: for positive integers `n` and `k`, part (i),

> Pf((j−i)𝓜^{(k)}_{i+j−2})_{1≤i,j≤2n} equals ∏_{i=0}^{m−1}∏_{j=0}^{k−1}(4ki+2j+k)
> if m = n/k is an integer, and it equals
> (∏_{j=1}^{⌊k/2⌋} 1/(2j−k))(∏_{i=0}^{m−1}∏_{j=1}^{k}(4ki+2j−k)) if k is odd and
> m = (n+⌊k/2⌋)/k is an integer. The Pfaffian is zero in all other cases.

and a part (ii) for the entries `𝓜^{(k)}_{i+j−2} + 𝓜^{(k)}_{i+j−1}`. The
authors remark that part (i) at `k = 1` is Theorem `thm.pfMotz` and that
their method does not apply for `k ≥ 2`, because the Pfaffians vanish
periodically.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1201.5253
- URL: https://arxiv.org/abs/1201.5253v2
- Version and location: arXiv:1201.5253v2 (2012-05-16), source file `pfaffians.tex`: the Pfaffian definition in the section "Pfaffians", Theorem `thm.pfMotz` in the section "A Motzkin Number Pfaffian", and Conjecture `conj.gen` at the end of the section "Application of Theorem 2".
