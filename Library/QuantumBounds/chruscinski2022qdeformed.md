---
bibkey: chruscinski2022qdeformed
authors: D. Chruściński, G. Kimura, H. Ohno, T. Singal
year: 2022
title: "Bounding the Frobenius norm of a q-deformed commutator"
doi: 10.48550/arXiv.2202.11520
url: https://arxiv.org/abs/2202.11520v2
claim: "For q > 0 the bound ‖AB − qBA‖²_F ≤ (1 + q²)‖A‖²_F‖B‖²_F holds when A or B is normal and can fail in general; Conjecture 1 asserts that it holds and is sharp when A or B is traceless, proved there for n = 2; Conjecture 2 asserts for q ≤ 0, A or B traceless, the sharp bound ‖[A,B]_q‖²_F ≤ max[g(n)(1−q)², 1+q²]‖A‖²_F‖B‖²_F with g(n) = (n²−3n+3)/(n(n−1))."
strata_touched:
  - D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation
  - D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation
license: citation-only
triage: anchor
---

# Chruściński, Kimura, Ohno and Singal, Frobenius norm of a q-deformed commutator

D. Chruściński, G. Kimura, H. Ohno and T. Singal, *Bounding the Frobenius norm of a q-deformed
commutator*, arXiv:2202.11520v2 (18 March 2022; math.QA, cross-listed math-ph); Linear Algebra
Appl. 646 (2022) 95–106.

## Verified locator

DOI: 10.48550/arXiv.2202.11520.
Primary version: https://arxiv.org/abs/2202.11520v2 (the latest arXiv version).
The TeX source `arxiv.tex` of v2 supplies the definition of the q-deformed commutator (§1),
Eq. (7), Proposition 1 (the normal case), Conjecture 1, Proposition 3, Eq. (24) and Conjecture 2
(§3, `arxiv.tex` lines 357–361, 483–485 and 503–509).

## Source statements

Definition (§1): "$[ \ A, B \ ]_q \ \coloneqq \ A B - q BA$ for a real parameter $q$", with the
Frobenius norm $\|A\|_F^2=\mathrm{tr}(A^\dagger A)$.

Eq. (7): "$\f{[A,B]_q}^2\leq\left(1+q^2 \right)\f{A}^2\f{B}^2$", proved "if either $A$ or $B$ is
normal", and "\eqref{eq:q_commutator_BW} can be violated if neither $A$ nor $B$ are normal."

Conjecture 1: "For any $q > 0$, if $A$ or $B$ is traceless, the inequality
\eqref{eq:q_commutator_BW} holds and is sharp." Followed by "we provide a proof of Conjecture
\ref{CON} for $n=2$ for any real $q$."

Proposition 3: "For $n=2$ and $\tr{A}=0$, the bound in Eq.~ \eqref{eq:q_commutator_BW} is satisfied
and is sharp."

Eq. (24): "$g(n) = \frac{n^2-3n+3}{n(n-1)}$".

Conjecture 2: "For any $q\le 0$, if $A$ or $B$ is traceless, the sharp bound is
${\f{[A,B]_q}^2} \ \leq \ \max[g(n)(1-q)^2, 1+q^2] \ \f{A}^2 \ \f{B}^2,$ where $g(n)$ is given by
\eqref{eq:gn}."

## Scope

The paper proves Conjecture 1 for $2\times2$ matrices and supports it numerically in higher
dimensions; the counterexample to the general form of (7) is a non-normal $2\times2$ pair with
nonzero traces. The value $g(n)(1-q)^2$ in Conjecture 2 is attained by $A=B=\operatorname{diag}(n-1,-1,\dots,-1)$, both traceless.
