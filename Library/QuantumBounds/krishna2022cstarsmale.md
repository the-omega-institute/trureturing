---
bibkey: krishna2022cstarsmale
authors: K. Mahesh Krishna
year: 2022
title: "C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture"
doi: 10.48550/arXiv.2206.08154
url: https://arxiv.org/abs/2206.08154v1
claim: "Conjecture HIGHERMEAN (journal Conjecture 2.3) asks for one critical point controlling every higher-order Smale ratio in a commutative C*-algebra; the paper proves the degree-2 case."
strata_touched:
  - D5/S3/Quantum/Algebra/CStarSmaleHigherOrder
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
Conjecture DUALSMALE of the same paper is treated separately in #14940.
The paper's CSMALE, its strong form and its dynamics conjecture are separate questions.
