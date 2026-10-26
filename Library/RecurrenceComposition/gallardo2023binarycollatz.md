---
bibkey: gallardo2023binarycollatz
authors: Luis H. Gallardo and Olivier Rahavandrainy
year: 2023
title: On Collatz Conjecture for binary polynomials
doi: 10.48550/arXiv.2308.01181
url: https://arxiv.org/abs/2308.01181v2
claim: "If A = (M² + M + 1)ⁿ with n ≥ 2, then ℓ_A equals n + 1."
strata_touched:
  - D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz
license: citation-only
triage: anchor
---

# Binary-polynomial Collatz length

## Verified locator

DOI: 10.48550/arXiv.2308.01181

Source: https://arxiv.org/abs/2308.01181v2

Conjecture 3.11 (p. 15): “If A = (M² + M + 1)ⁿ with n ≥ 2, then ℓ_A equals n + 1.”

The definitions on p. 2 say: “we say ([3]) that A is odd if gcd(A, x(x + 1)) = 1,
i.e., if it has no linear factor.” They also say: “The first odd polynomial
after 1 is M := x² + x + 1.” The odd part is specified by
“S = x^{val_x(S)}(x + 1)^{val_{x+1}(S)} S₁, where S₁ is odd.”

The transformations on p. 2 specify “A₁ the odd polynomial such that
A₀ = x^{a₀}(x + 1)^{b₀}A₁”, “A_{2k} = 1 + MA_{2k−1}”, and
“A_{2k+1} = A_{2k}/(x^{a_{2k}}(x + 1)^{b_{2k}}).”

Theorem 1.2 (p. 3) gives “[A₀, …, A_{2m−2}, x² + x] and
[A₁, …, A_{2m−1}, 1]” and “where m ∈ ℕ*, ℓ_A = m + 1 ≤ 2^{deg(A)−1}.”
Thus the length counts the initial odd term and the terminal 1. The example
n=9 on p. 15 has length 10 and the degree sequence
[36, 32, 32, 32, 32, 32, 30, 30, 4, 0].

The Lean encoding uses Polynomial (ZMod 2), rootMultiplicity at 0 and 1,
and divByMonic. The source's oddness predicate is IsCoprime A (X*(X+1)).
The natural index k selects A_{2k+1}; collatzLength is the first index at
which this sequence reaches 1, plus one. Polynomial reversal and composition
with x(x+1) transport the process to a degree-controlled map. Its two
hitting-time identities for squaring and multiplying a square by
1+X+X² prove the conjecture by binary induction, also covering n=0 and n=1.

The literature screen is recorded in
https://github.com/the-omega-institute/trureturing/issues/19299.
Completeness of prior-art coverage is ASSUMED-UNVERIFIED; the screen leaves
the full text of Hicks–Mullen–Yucas–Zavislak and detailed Nichols proof
passages unverified. The general upper bound in Theorem 1.2 and its possible
improvement are separate from the exact family settled here.

The finite corroboration is in the private repository
https://github.com/the-omega-institute/trureturing-experiments at commit
85b4f93c, path docs/reports/gallardo-rahavandrainy-2023-binary-collatz-3-11/check.py,
SHA-256 86f968206e76be2c8db4d0ce65d68113ff1e64d43beee8bf64c8240fab8b6e12.
The preregistration records exit 0 and RESULT PASS. These computations are
corroboration; the universal conclusion is established by the Lean proof.
