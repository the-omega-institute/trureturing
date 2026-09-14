---
bibkey: benfield2025jacobsthal
authors: Brennan Benfield; Oliver Lippard
year: 2025
title: Fixed Points of K-Fibonacci Sequences
doi: 10.1080/00150517.2025.2491986
claim: Conjecture 6.3 is proved below for the explicit least eventual-period convention; pure periodicity and the scope of the uncompiled Lean companion are distinguished.
strata_touched:
  - D5/S1/Recurrence/JacobsthalTailPeriod
license: citation-only
triage: anchor
---

# Jacobsthal fixed points and the effect of powering the golden unit

## 1. The external problem and the meaning of period

Benfield and Lippard, *Fixed Points of K-Fibonacci Sequences*, Conjecture 6.3,
asks whether the Jacobsthal period fixed points greater than one are exactly
`2*3^k`, with `k>=1`. Both arXiv:2404.08194v2 and the retrieved publisher's
2025 version retain this conjecture [1].

The source recurrence is

\[
J_0=0,\qquad J_1=1,\qquad J_{n+2}=J_{n+1}+2J_n.
\]

Its companion has determinant -2. Every positive-index Jacobsthal number is
odd, so at an even modulus there is no positive period valid from index zero.
Define lambda_J(m) to be the **least eventual period**: the least t>0 for
which some N satisfies J_(n+t)=J_n modulo m for every n>=N. Define mu_J(m)
to be the least starting index of the periodic tail.

OEIS A175286 records the period values `1,1,6,2,4,6,6,2,18,...` at moduli
1,2,3,... [2], consistent with this eventual-period convention. The proof below
establishes the conjectured family under this explicit convention. Under a
strict pure-period interpretation the proposed even moduli have no period.
No inference silently identifies these two conventions.

## 2. An exact criterion at every tail start

**Lemma 2.1.** For every n>=0,

\[
J_{n+1}=2J_n+(-1)^n,\qquad 3J_n=2^n-(-1)^n.
\]

*Proof.* The first equality follows by induction from the original recurrence,
and the second by induction from the first. In particular J_n is odd for n>0.
The identities are over the integers, with no modular division by three.

For D_n=J_(n+t)-J_n, the first equality gives

\[
D_{n+1}-2D_n=(-1)^n\bigl((-1)^t-1\bigr).\tag{2.1}
\]

**Theorem 2.2.** For every m>2 and every N,t>=0,

\[
\left(\forall n\ge N:\ m\mid J_{n+t}-J_n\right)
\iff \left(t\text{ is even and }m\mid2^N J_t\right).\tag{2.2}
\]

*Proof.* Two consecutive differences in (2.1) force m to divide (-1)^t-1.
Odd t would give m|2, impossible for m>2. For even t, Lemma 2.1 gives

\[
J_{n+t}-J_n=2^nJ_t.\tag{2.3}
\]

The forward direction uses n=N. The reverse direction follows by multiplying
the divisibility at N by 2^(n-N). The zero shift is included in (2.2).

The Lean companion supplies proof scripts for the original recurrence,
Theorem 2.2 and the absence of positive pure periods at even moduli. These
scripts have not been elaborated or kernel-checked in this environment.
The full fixed-point classification below is an ordinary mathematical proof.

## 3. Complete period and preperiod formulas

Write m=2^a*d with d odd and positive. For m>2 and **every positive shift t**,
Theorem 2.2 is equivalent to

\[
N\ge a\quad\text{and}\quad3d\mid2^t-1.\tag{3.1}
\]

Indeed, d is coprime to 2^N, and for even t the integer identity
3J_t=2^t-1 gives d|J_t iff 3d|2^t-1. Conversely the latter congruence forces
t even by reduction modulo three. Since J_t is odd when t>0, the power of
two in m divides 2^N J_t exactly when N>=a. The positive-shift condition is
essential in (3.1); (2.2), unlike (3.1), also permits t=0.

Euler's theorem guarantees an exponent returning 2 modulo the odd number 3d.
Thus (3.1) proves both existence and minimality in

\[
\boxed{\lambda_J(m)=\operatorname{ord}_{3d}(2),\qquad
\mu_J(m)=a\quad(m>2).}\tag{3.2}
\]

The small moduli satisfy

\[
(\mu_J(1),\lambda_J(1))=(0,1),\qquad
(\mu_J(2),\lambda_J(2))=(1,1).\tag{3.3}
\]

Pure periodicity occurs exactly at odd positive moduli. The factor three in
(3.2) matters: lambda_J(3)=ord_9(2)=6, whereas ord_3(2)=2.

## 4. Conjecture 6.3 under the eventual-period convention

**Theorem 4.1.** For every m>1,

\[
\boxed{\lambda_J(m)=m\iff m=2\cdot3^k\text{ for some }k\ge1.}\tag{4.1}
\]

*Necessity.* The modulus two is excluded by (3.3). Every positive period for
m>2 is even, so a fixed point has a decomposition

\[
m=2^a3^b s,\qquad a\ge1,\quad b\ge0,\quad\gcd(s,6)=1.
\]

Euler's theorem and multiplicativity of the totient give

\[
2^a3^b s=m=\lambda_J(m)
\le\varphi(3^{b+1}s)=2\cdot3^b\varphi(s)
\le2\cdot3^b s.\tag{4.2}
\]

All cancelled factors are positive. Hence a=1 and equality forces
varphi(s)=s. The inequality varphi(s)<s for s>1 gives s=1. Since m>2,
b>=1, as required.

*Sufficiency.* For every h>=1,

\[
v_3(4^h-1)=1+v_3(h).\tag{4.3}
\]

For completeness, if 3 does not divide h, the geometric quotient
(4^h-1)/(4-1) is h modulo three and is prime to three. If x=1+3u, then
x^2+x+1=3*(1+3u+3u^2) has exact valuation one. Factoring
x^3-1=(x-1)(x^2+x+1) shows that tripling an exponent adds exactly one to
its valuation. Decompose h into a power of three and a factor prime to three
to obtain (4.3).

Every positive t with 2^t=1 modulo 3^(k+1) is even, say t=2h. Equation (4.3)
shows that this happens exactly when 3^k|h. Therefore

\[
\operatorname{ord}_{3^{k+1}}(2)=2\cdot3^k.
\]

Formula (3.2) at m=2*3^k completes sufficiency and minimality; the preperiod is
one. This is one external numbered conjecture. The recurrence identities,
totient theorem, lifting lemma and intermediate period formulas are not
additional resolved-problem counts or rediscovery claims.

## 5. Genuine golden powers and the actual companion basis

Fix t>=1, u=phi^t, a_t=F_(t-1), L_t=trace(u), and nu_t=(-1)^t. Define

\[
U^{(t)}_0=0,\quad U^{(t)}_1=1,\quad
U^{(t)}_{n+2}=L_tU^{(t)}_{n+1}-\nu_t U^{(t)}_n.\tag{5.1}
\]

The actual golden ring gives

\[
\boxed{F_{tn}=F_tU^{(t)}_n.}\tag{5.2}
\]

For n>=1, compare the golden coordinates in
u^n=U_n^(t)*u-nu_t*U_(n-1)^(t), an induction using the quadratic
characteristic identity. The case n=0 is immediate.

In the original basis (1,phi), multiplication by u and its companion satisfy

\[
M_t=\begin{pmatrix}a_t&F_t\\F_t&a_t+F_t\end{pmatrix},\quad
B_t=\begin{pmatrix}0&-\nu_t\\1&L_t\end{pmatrix},\quad
K_t=\begin{pmatrix}1&a_t\\0&F_t\end{pmatrix},
\qquad M_tK_t=K_tB_t,\quad\det K_t=F_t.
\tag{5.3}
\]

Let tau_t(m) denote the least complete sequence period of (5.1). Its companion
determinant is nu_t, a unit, so it is purely periodic modulo every positive m.
The period equals the order of B_t. Indeed e_1 and B_t e_1=e_2 are a basis,
and B_t^n e_1 has coordinates (U_(n+1)^(t)-L_t U_n^(t), U_n^(t)). A return of
the consecutive sequence pair fixes e_1 and hence its image e_2. This proves
the equality of the two genuine periods without a postulated basis change.

## 6. Exact prime-power periods in both basis cases

Fix a prime p different from two and five, and put

\[
r_p=\pi(p),\qquad c_p=v_p(F_{p-(5/p)}),\qquad v=v_p(t).
\]

Classical Fibonacci valuation and period lifting, also retained in
PERIODIC_TREE Appendix R, give p not dividing r_p, c_p>=1, and

\[
\pi(p^e)=r_p p^{\max(e-c_p,0)},\qquad e\ge1.\tag{6.1}
\]

The initial depth c_p is arbitrary. Lengyel's rank-based formula [3] identifies
the valuations at the rank, signed Frobenius index and complete period,
because the relevant multipliers are prime to p. The condition c_p>=2 is
exactly classical WSS.

**Theorem 6.1.** If p does not divide F_t, then for every e>=1,

\[
\boxed{\tau_t(p^e)=\frac{r_p}{\gcd(r_p,t)}
 p^{\max(e-c_p-v_p(t),0)}.}\tag{6.2}
\]

*Proof.* K_t is invertible modulo p^e. Thus B_t and multiplication by phi^t
have the same order. For an element of finite order R, its t-th power has
order R/gcd(R,t). Substitute R from (6.1) and use p not dividing r_p to obtain

\[
\gcd(r_p p^j,t)=\gcd(r_p,t)p^{\min(j,v_p(t))}.
\]

Subtracting the exponents proves (6.2).

**Theorem 6.2.** Suppose p divides F_t. Let lambda=a_t modulo p, and let delta
be its multiplicative order. Then delta belongs to {1,2,4}, and for every e>=1,

\[
\boxed{\tau_t(p^e)=\delta p^e.}\tag{6.3}
\]

*Proof.* The unit u reduces to the nonzero scalar lambda. Its norm gives
lambda^2=nu_t, so delta divides four. Equation (5.2) and the valuation theorem
imply, for every n>0,

\[
v_p(U^{(t)}_n)=v_p(F_{tn})-v_p(F_t)=v_p(n).\tag{6.4}
\]

A return modulo p^e therefore requires p^e|n. Modulo p, write
B_t=lambda*I+D with D^2=0, by its repeated-root characteristic polynomial.
When p|n, its n-th power is lambda^n I. A return also requires delta|n.

Conversely, suppose delta*p^e|n. Then U_n^(t)=0 modulo p^e. The companion
identity B_t^n=U_n^(t)B_t-nu_t U_(n-1)^(t)I makes this a scalar matrix cI.
Modulo p it equals lambda^n I=I, so c=1 modulo p. Its determinant gives
c^2=nu_t^n=1: if nu_t=-1, then delta=4, so n is even. Thus c+1 is a unit
modulo p^e. From (c-1)(c+1)=0, conclude c=1. The two necessary divisibilities
have coprime moduli, proving exact minimality in (6.3).

**Corollary 6.3.** For every t>=1 and p!=2,5 prime,

\[
\boxed{\tau_t(p^2)=\tau_t(p)
\iff p\nmid F_t\ \land\
\bigl(p\text{ is classical WSS}\ \lor\ p\mid t\bigr).}\tag{6.5}
\]

The singular case (6.3) has no plateau. In (6.2), a plateau is equivalent to
c_p+v_p(t)>=2. Since c_p>=1, this is the displayed alternative.

Thus p|t can manufacture a derived-sequence plateau. At p|F_t, dividing the
subsequence by F_t cancels the initial depth and the companion has no plateau.
Only for p not dividing t*F_t does the derived plateau coincide with classical
WSS. For fixed t, there are finitely many primes in the two exceptional sets;
outside them the equivalence supplies no additional constraint across primes.

For example t=p=3 gives L_t=4 and F_t=2. The derived periods modulo three
and nine are both eight, while the original Fibonacci periods are eight and
24. This is no classical WSS witness. For t=8 and p=3, the singular basis gives
tau_8(3^e)=3^e, agreeing with the a=47 family already treated in PR #7709.

## 7. Prior art and remaining WSS question

The exact Conjecture 6.3 was checked in both primary arXiv v2 and the retrieved
publisher's 2025 text. The A175286 entry was checked for the period convention.
Searches of the title, authors, conjecture number, Jacobsthal fixed points,
modular periods and multiplicative order found no earlier proof of this exact
fixed-point assertion in the returned sources. GitHub results included an
A175286 LODA term-generating program and the repository's old digit-gas
Jacobsthal specializations. Neither proves the classification. The general
period formula is not separately claimed new. Search coverage, worldwide
priority and editorial acceptance remain unconfirmed.

Ross, Shen and Cai [4], Corollary 5.1, already prove that absence of classical
WSS primes is equivalent to squarefreeness of all Fibonacci multiplicative
Mobius duals except index six. This related lead is therefore not a new
resolution or new equivalence here.

No prime with c_p>=2 has been established, and no universal theorem c_p=1
has been proved. Equations (6.2)-(6.5) characterize precisely the information
available from genuine golden powering. The Jacobsthal fixed-point theorem
closes the explicitly stated eventual-period version of a neighboring target;
it does not resolve WSS existence.

## References

[1] Brennan Benfield and Oliver Lippard. *Fixed Points of K-Fibonacci Sequences*.
Fibonacci Quarterly, 2025, pp. 259-274. DOI: 10.1080/00150517.2025.2491986.
Conjecture 6.3. arXiv:2404.08194v2, July 29, 2024.
https://arxiv.org/html/2404.08194v2
https://www.tandfonline.com/doi/full/10.1080/00150517.2025.2491986

[2] R. J. Mathar. OEIS A175286, *Pisano period of the Jacobsthal sequence A001045
modulo n*, March 21, 2010. https://oeis.org/A175286

[3] Luis A. Medina and Eric Rowland. *p-regularity of the p-adic valuation of the
Fibonacci sequence*. Fibonacci Quarterly 53 (2015), 265-271. Theorems 1.2 and 1.4.
https://arxiv.org/abs/0910.2907

[4] Tyler Ross, Zhongyan Shen and Tianxin Cai. *The p-adic Valuations of Mobius
Duals of Lucas Sequences*. arXiv:2512.03481v1, December 3, 2025, Corollary 5.1.
https://arxiv.org/html/2512.03481v1

## Formalization boundary

Sections 2-6 contain complete ordinary mathematical proofs. The Lean companion
covers the original recurrence, exact all-tail criterion (2.2), and absence of
positive pure periods at even moduli. The totient classification (4.1) and
golden-power formulas (6.2)-(6.5) have not been formalized in this submission.
The new Lean script has not been elaborated; no Lean/lake executable is
available here. No C# or Scribe execution was performed. No custom axiom,
admitted proof, resolution marker, freeze, CI pass or independent multi-model
review is claimed.
