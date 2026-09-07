# Shankar Q closed-form Stieltjes obstruction

Source: Umesh Shankar, *Avoiding patterns with three distinct letters in
Canon permutations*, arXiv:2608.30002v2, 1 September 2026,
https://arxiv.org/html/2608.30002v2, sections 2.2, 2.7, 7, and 9.
Conjecture 9.5 asserts that both B and Q are Stieltjes moment sequences.
The Q sequence counts words with k copies of 1, 2, and 3, with every
prefix satisfying #1 >= #2 >= #3 and with no 321 subsequence; Q_0=1.
The following obligation targets precisely the closed form identified
with that count by the paper's Theorem 7.1. That combinatorial identity
is a published input to the source interpretation, not a Lean axiom or
a claimed kernel-verified bijection. B remains unresolved by this result.

## Theorem: The source closed form has no Stieltjes representation

For an integer lower index j, let binom(m,j)=0 when j<0 or j>m,
and otherwise let it be the usual binomial coefficient. Define q(0)=1
and, for each natural k>=1, define

\[
q(k)=\frac{\binom{2k}{k}}{k+1}
 +\sum_{b=1}^{k-1}\sum_{c=0}^{b}
 \left[\binom{2k-b-c}{k-b}-\binom{2k-b-c}{k-b-1}\right]
 \sum_{r=b}^{k-1}
 \left[\binom{r+b-1}{b-1}-\binom{r+b-1}{b-2}\right]
 \binom{k-1-r+c}{c}.
\]

There is no positive Borel measure mu on the real line concentrated on
the nonnegative half-line such that every monomial is integrable and

\[
\int_{\mathbb R} t^n\,d\mu(t)=q(n)\qquad(n\in\mathbb N).
\]

The intended refutation uses an integer polynomial p of degree ten:
the exact quadratic form involving q(i+j+3) is strictly negative,
whereas any such representation makes it the nonnegative integral of
t^3 p(t)^2. The claim is a refutation of the Q part of Conjecture 9.5
through the source's Theorem 7.1; no conclusion about B is asserted.
