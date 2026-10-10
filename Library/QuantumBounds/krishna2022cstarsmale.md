---
bibkey: krishna2022cstarsmale
authors: K. Mahesh Krishna
year: 2022
title: "C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture"
doi: 10.48550/arXiv.2206.08154
url: https://arxiv.org/abs/2206.08154v1
claim: "Conjecture HIGHERMEAN (journal Conjecture 2.3) and Conjecture DUALSMALE (Conjecture 3.1) ask for a critical point controlling the Smale ratios, respectively the Dubinin-Sugawa dual ratio, in a commutative C*-algebra; the paper proves both degree-2 cases."
strata_touched:
  - D5/S3/Quantum/Algebra/CStarSmaleHigherOrder
  - D5/S3/Quantum/Algebra/CStarDualMeanValue
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2206.08154

Source: https://arxiv.org/abs/2206.08154v1

Journal DOI: 10.26117/2079-6641-2026-54-2-38-47

# Krishna, C*-algebraic Smale mean value conjectures

K. Mahesh Krishna, *C*-algebraic Smale Mean Value Conjecture and
Dubinin-Sugawa Dual Mean Value Conjecture*, arXiv:2206.08154v1, Section 2.
The journal version appears in *Vestnik KRAUNC Fiz.-Mat. Nauki* 54(2), 38–47,
and labels HIGHERMEAN as Conjecture 2.3 on p. 44.

## Source statement

**Conjecture HIGHERMEAN (Higher Order C*-algebraic Smale Mean Value Conjecture).**

> Let $\mathcal{A}$ be a commutative C*-algebra. Let $P(z)\coloneqq (z-a_1)\cdots (z-a_n)$ be a polynomial of degree $n\geq 2$ over $\mathcal{A}$, $a_1, \dots, a_n \in \mathcal{A}$. If $z\in\mathcal{A}$ is not a critical point of $P$, then there exists a critical point $w\in \mathcal{A}$ of $P$ such that
>
> $$
> \frac{\|P^{(k)}(z)\|}{k!}\frac{\|P(z)-P(w)\|^{k-1}}{\|P'(z)\|^k}
> \leq 4^{k-1}, \quad \forall 2\leq k\leq n.
> $$

The following theorem states: “Conjecture 2.3 holds for degree 2 C*-algebraic
polynomials.” In the journal this is Theorem 2.2, p. 44.
The scalar Higher Order Smale Mean Value Theorem is Theorem 1.3 in the
journal; the C*-algebraic extension is a distinct statement.

## Encoding and scope

`smalePoly` is the literal product of the factors `Polynomial.X - Polynomial.C (a j)`
for `j : Fin n`; the index `j` represents the source's `a_(j+1)`.
The source's sum-of-omitted-factors derivative is `Polynomial.derivative_prod`,
and higher derivatives are iterates of `Polynomial.derivative`.
The unital complex commutative C*-algebra convention is `CommCStarAlgebra`.
A refutation on `Complex × Complex` suffices for the source's universal claim,
including any broader interpretation allowing non-unital algebras.

The degree-three refutation uses the supremum norm on `Complex × Complex`.
It does not alter the degree-2 theorem or the scalar theorem.
The paper's CSMALE, its strong form and its dynamics conjecture are separate questions.

## Conjecture DUALSMALE

Section 2, p. 4, defines the polynomial and its derivative:

> Let 𝒜 be a C*-algebra. For P(z) ≔ (z−a₁)(z−a₂)⋯(z−aₙ) for all z∈𝒜 with a₁, a₂, …, aₙ ∈ 𝒜, we define P′(z)=∑ⱼ₌₁ⁿ (z−a₁)⋯(z−aⱼ)̂⋯(z−aₙ), ∀z∈𝒜 where the term with cap is missing.

The derivative is the sum of ordered products with one factor omitted. The
gloss in Conjecture CSMALE (Conjecture 2.1, p. 4) is “If z∈𝒜 is not a critical
point of P (i.e., P′(z)≠0)”.

Section 3, p. 7, states Conjecture DUALSMALE (Conjecture 3.1):

> **C*-algebraic Dubinin-Sugawa Dual Mean Value Conjecture.** Let 𝒜 be a commutative C*-algebra. Let P(z) ≔ (z−a₁)⋯(z−aₙ) be a polynomial of degree n ≥ 2 over 𝒜, a₁, …, aₙ ∈ 𝒜. If z∈𝒜 is not a critical point of P, then there exists a critical point w∈𝒜 of P such that ‖P′(z)‖/deg(P) = ‖P′(z)‖/n ≤ ‖P(z)−P(w)‖/‖z−w‖.

The same norm-form assertion is Conjecture 3.1 in the journal version.
Theorem 3.3 of the arXiv version (p. 7), numbered Theorem 3.1 in the journal,
states:

> Conjecture 3.1 holds for degree 2 C*-algebraic polynomials.

For degree two the sole critical point is (a₁+a₂)/2 and the norm inequality
is an equality. This result is distinct from the degree-three refutation.

The Lean encoding uses zero-based Fin n indices and the ordered product
`(List.ofFn fun i => z - a i).prod`. It reuses the ordered derivative of
`CStarSchoenberg`. Noncritical means that derivative is nonzero; critical
means that it is zero. The degree parameter n is cast to ℝ in the norm
inequality. The carrier is restricted to unital commutative C*-algebras in
Type, weakening the source's universal assertion; a counterexample in that
subclass refutes the source statement.
