---
bibkey: beluhov2026diamond
authors: Nikolai Beluhov
year: 2026
title: "Diamond Determinants and Somos Sequences"
doi: null
url: https://arxiv.org/abs/2602.24239v2
claim: "Conjecture 3: For every proper type 𝐧 of order n, it holds that dim Ω⊠ = ⌊n/2⌋."
strata_touched:
  - D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation
license: citation-only
triage: anchor
---

# Beluhov's invariant-kernel dimension conjecture

## Verified locator

URL: https://arxiv.org/abs/2602.24239v2

The quotations refer to the printed pages of arXiv:2602.24239v2.
Conjecture 3, page 24, states:

> For every proper type 𝐧 of order n, it holds that dim Ω⊠ = ⌊n/2⌋.

The surrounding paragraph on page 24 states:

> For any proper type 𝐧, we can define the space ℰ as in Section 2; it is not too difficult to see that ℰ will still depend only on the parity of n.

## Source definitions

Section 10, page 23:

> Let 𝐧 = (n₁, n₂, n₃) with n₁, n₂, n₃ being positive integers such that n = n₁ + n₂ + n₃.

Section 10, page 24:

> We call a type 𝐧 proper if it is primitive and n₁, n₂, n₃ are pairwise distinct.

Primitive means that the joint gcd of the entries is one. The quadratic
recurrence form is

$$
R_{\mathbf n}=a x_{n_1}x_{n_2+n_3}
 +b x_{n_2}x_{n_3+n_1}+c x_{n_3}x_{n_1+n_2}.
$$

The coefficient field is the rational-function field in the three
independent recurrence coefficients. The Lean representation is
`FractionRing (MvPolynomial (Fin 3) ℚ)`; rational-function fields formed
from integer or rational polynomial coefficients are the same here.

Section 5, page 11:

> This is equivalent to each exponent tuple (d₀, d₁, …, dₙ₋₁) which occurs in Φ satisfying d₀e₀ + d₁e₁ + ⋯ + dₙ₋₁eₙ₋₁ = e₀ + e₁ + ⋯ + eₙ₋₁ for all integer e ∈ ℰ.

> The polynomials Φ which satisfy our additional constraint form a linear subspace Υ⊠ of Υ.

> Let Ω⊠ be the kernel of φ over Υ⊠.

The source's parity-only gauge bases on page 5 are `1,i` for even order
and `i,i mod 2,(i+1) mod 2` for odd order. Thus the admissible degree-n
monomials have exponent sum n and index-weight sum n(n−1)/2; odd order
also requires even-index exponent sum (n+1)/2 and odd-index exponent
sum n/2. These quotients are natural integer divisions.

The operator in Section 5, page 10 is

$$
\varphi_t(\Phi)=x_0^{n-2}R_t\Phi
 -\Phi(x_0x_1,x_0x_2,\ldots,x_0x_{n-1},R_t).
$$

## Formal scope

The formal claim follows the source's stated parity-only gauge reading.
It quantifies over all proper types, using the K-dimension of the
intersection of the admissible monomial span with the kernel of the
displayed operator. The refutation uses type (1,3,6), of order 10, over
the independent-parameter field K, and six independent kernel elements.
It establishes a lower bound of six, rather than a matching upper bound.

The full gauge space determined by only the three nonzero terms of this
type's recurrence is a different interpretation. Its dimension and
restricted kernel dimension are not proved by this module. Conjectures
1, 2 and 4–6 are outside the refutation's formal conclusion. The source's
verified low-order results are not contradicted by this order-10 example.
