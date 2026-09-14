---
bibkey: benfield2025jacobsthal
authors: Brennan Benfield; Oliver Lippard
year: 2025
title: Fixed Points of K-Fibonacci Sequences
doi: 10.1080/00150517.2025.2491986
claim: Conjecture 6.3 specifies Jacobsthal fixed points; the original proof below classifies them for the explicit least eventual-period convention and distinguishes pure periodicity.
strata_touched:
  - D5/S1/Recurrence/JacobsthalTailPeriod
license: citation-only
triage: anchor
---

# Jacobsthal fixed points and the effect of powering the golden unit

## 1. The external problem and the meaning of period

Brennan Benfield and Oliver Lippard, *Fixed Points of K-Fibonacci Sequences*,
Conjecture 6.3, asks whether the Jacobsthal period fixed points greater than
one are exactly `2*3^k`, with `k>=1`. The statement occurs in arXiv:2404.08194v2
and in the publisher's 2025 version, DOI 10.1080/00150517.2025.2491986 [1].

There is a necessary convention to resolve. The Jacobsthal recurrence is

\[
J_0=0,\quad J_1=1,\quad J_{n+2}=J_{n+1}+2J_n.
\]

Its companion has determinant -2. At every even modulus the sequence has a
nonempty preperiod. In particular, it has no positive period valid from index
zero, because every J_n with n>0 is odd. The relevant period map is therefore
the **least eventual period**, denoted lambda_J(m): the least positive t for
which there is N such that J_(n+t)=J_n modulo m for every n>=N. The initial
transient length is denoted mu_J(m).

OEIS A175286 independently records the period values with initial terms
`1,1,6,2,4,6,6,2,18,...` at moduli 1,2,3,... [2]. These agree with the eventual
period convention, including its noninvertible even moduli. The theorem below
proves the conjectured family for this explicit convention. Under a strict
pure-period interpretation, none of its proposed even moduli has such a
period. These two assertions are kept separate.

## 2. An exact criterion at every tail start

**Lemma 2.1.** For all n>=0,

\[
J_{n+1}=2J_n+(-1)^n,\qquad 3J_n=2^n-(-1)^n.
\]

*Proof.* The first identity follows by induction from the original recurrence,
and the second follows by induction from the first. In particular, J_n is odd
for every positive n. No division modulo three is used.

For a modulus m and a shift t define D_n=J_(n+t)-J_n. The first identity gives

\[
D_{n+1}-2D_n=(-1)^n\bigl((-1)^t-1\bigr).
\tag{2.1}
\]

**Theorem 2.2.** For every m>2 and all N,t>=0,

\[
\left(\forall n\ge N:\ m\mid J_{n+t}-J_n\right)
\quad\Longleftrightarrow\quad
\left(t\text{ is even and }m\mid 2^N J_t\right).
\tag{2.2}
\]

*Proof.* Applying the left-hand assertion at N and N+1 in (2.1) gives
m dividing (-1)^t-1. Odd t would force m to divide 2, which contradicts m>2.
For even t, the two closed forms in Lemma 2.1 give the exact integer equality

\[
J_{n+t}-J_n=2^nJ_t.\tag{2.3}
\]

The forward direction now follows by taking n=N. Conversely, divisibility at
N persists at every n=N+k because its right side is multiplied by 2^k. This
also handles t=0; a genuine period is additionally required to be positive.

The accompanying Lean script proves Theorem 2.2 for the actual recurrence,
with every N and t quantified, and proves the absence of a positive pure
period for every even modulus. It does not assume the desired classification
as a field of a structure or as an input hypothesis.

## 3. Complete period and preperiod formulas

Write m=2^a*d, with d odd and positive. For m>2, Theorem 2.2 and the oddness of
J_t for positive even t imply that the shift works from N precisely when

\[
N\ge a\quad\text{and}\quad 3d\mid 2^t-1.\tag{3.1}
\]

Indeed, the odd factor d is coprime to 2^N, so d|2^N J_t iff d|J_t.
Since 3J_t=2^t-1 for even t, this is equivalent to 3d|2^t-1 **in the integers**.
Conversely the latter congruence forces t even by reduction modulo three.
The power-of-two part divides 2^N J_t exactly when a<=N because J_t is odd.

Euler's theorem guarantees a positive exponent with 2^t=1 modulo the odd
number 3d. Therefore the complete formulas are

\[
\boxed{\lambda_J(m)=\operatorname{ord}_{3d}(2),\qquad
\mu_J(m)=a\quad(m>2).}\tag{3.2}
\]

The two small moduli are

\[
(\mu_J(1),\lambda_J(1))=(0,1),\qquad
(\mu_J(2),\lambda_J(2))=(1,1).\tag{3.3}
\]

Equation (3.1) proves minimality of both quantities, rather than merely
exhibiting a period. It also proves that pure periodicity occurs exactly at
odd positive moduli. In particular the factor 3 in the order modulus cannot
be discarded; at m=3 the period is ord_9(2)=6, not ord_3(2)=2.

## 4. Proof of Conjecture 6.3 with the eventual-period convention

**Theorem 4.1.** For every integer m>1,

\[
\boxed{\lambda_J(m)=m\quad\Longleftrightarrow\quad
m=2\cdot3^k\text{ for some }k\ge1.}\tag{4.1}
\]

*Necessity.* The modulus 2 is excluded by (3.3). If m>2 is a fixed point,
(3.1) shows that its period m is even. Write

\[
m=2^a3^b s,\qquad a\ge1,\quad b\ge0,\quad \gcd(s,6)=1.
\]

Euler's theorem, multiplicativity of the totient, and (3.2) give

\[
2^a3^b s=m=\lambda_J(m)
\le\varphi(3^{b+1}s)=2\cdot3^b\varphi(s)
\le2\cdot3^b s.
\tag{4.2}
\]

All factors cancelled here are positive. Hence a=1. Equality also forces
phi(s)=s. The elementary bound phi(s)<s for s>1 implies s=1. Since m>2,
b>=1, proving necessity.

*Sufficiency and minimality.* For every h>=1,

\[
v_3(4^h-1)=1+v_3(h).\tag{4.3}
\]

Here is an elementary proof, so the sufficiency direction has no unproved
lifting assumption. If 3 does not divide h, the quotient
(4^h-1)/(4-1)=1+4+...+4^(h-1) is h modulo three and is a unit there. If x=1
modulo three, then writing x=1+3u gives
x^2+x+1=3*(1+3u+3u^2), which has exact valuation one at three. Factoring
x^3-1=(x-1)*(x^2+x+1) shows that multiplying the exponent by three increases
the valuation by exactly one. Factoring h into a power of three times an
integer prime to three proves (4.3).

Any exponent t with 2^t=1 modulo 3^(k+1) is even, say t=2h. Formula (4.3)
shows that the congruence holds exactly when 3^k divides h. Therefore

\[
\operatorname{ord}_{3^{k+1}}(2)=2\cdot3^k.
\]

Apply (3.2) at m=2*3^k. Its least eventual period is exactly m, and its
preperiod is exactly one. This completes both directions for all m>1.

There is one numbered external conjecture here. The period formula, the
preperiod formula, and the elementary lifting lemma are not additional
solved-problem counts. The recurrence identities, Euler's theorem and the
three-adic lifting mechanism are classical; no rediscovery claim is made.

## 5. The WSS problem under genuine golden powering

A useful comparison with the noninvertible Jacobsthal recurrence is provided
by the golden unit, whose norm is -1. All of its powers remain units. Yet a
companion basis built from a power can become singular modulo a prime.

Fix t>=1. Put u=phi^t, a_t=F_(t-1), L_t=trace(u), and nu_t=(-1)^t. Define the
actual power-subsequence companion recurrence

\[
U^{(t)}_0=0,\quad U^{(t)}_1=1,\quad
U^{(t)}_{n+2}=L_tU^{(t)}_{n+1}-\nu_t U^{(t)}_n.
\tag{5.1}
\]

The golden identity gives

\[
\boxed{F_{tn}=F_tU^{(t)}_n.}\tag{5.2}
\]

For n>=1, one proof compares coefficients of phi in
u^n=U_n^(t)*u-nu_t*U_(n-1)^(t), derived by induction from the quadratic
characteristic identity; n=0 is immediate. Let tau_t(m) be the least complete
sequence period of (5.1). Because nu_t is a unit, this sequence is purely
periodic modulo every positive m, unlike Jacobsthal at even m.

Use the basis (1,phi) of the original golden ring. Multiplication by u and the
companion in the cyclic basis (1,u) are

\[
M_t=\begin{pmatrix}a_t&F_t\\F_t&a_t+F_t\end{pmatrix},\quad
B_t=\begin{pmatrix}0&-\nu_t\\1&L_t\end{pmatrix},\quad
K_t=\begin{pmatrix}1&a_t\\0&F_t\end{pmatrix}.
\]

Direct multiplication gives M_t*K_t=K_t*B_t and det(K_t)=F_t. Also the complete
sequence period equals the order of B_t: the initial cyclic vector and its
image are a basis, and the two coordinates of B_t^n on that vector are
U_(n+1)^(t)-L_t*U_n^(t) and U_n^(t). Returning the full consecutive sequence
pair is therefore equivalent to returning the matrix to the identity. These
are statements about the specified original integer objects, with no
postulated change of basis.

## 6. Exact prime-power periods in both basis cases

Fix a prime p different from 2 and 5, and put

\[
r_p=\pi(p),\quad c_p=v_p(F_{p-(5/p)}),\quad v=v_p(t).
\]

The classical Fibonacci valuation and period-lifting theorems give
p not dividing r_p, c_p>=1, and

\[
\pi(p^e)=r_p\,p^{\max(e-c_p,0)},\qquad e\ge1.
\tag{6.1}
\]

These are the same signed-index and prime-power statements retained in
PERIODIC_TREE, Appendix R. The value c_p is left arbitrary; c_p>=2 is exactly
the classical WSS condition. Lengyel's rank-based formula, recorded by
Medina and Rowland [3], identifies the initial valuation at the rank,
at p-(5/p), and at the complete period, since the relevant multipliers are
prime to p.

**Theorem 6.1, invertible basis.** If p does not divide F_t, then for every e>=1,

\[
\boxed{\tau_t(p^e)=\frac{r_p}{\gcd(r_p,t)}\,
 p^{\max(e-c_p-v_p(t),0)}.}\tag{6.2}
\]

*Proof.* The determinant of K_t is a unit modulo p^e, so B_t and multiplication
by phi^t have the same order. The order of the t-th power of an element of
finite order R is R/gcd(R,t). Substitute R=pi(p^e) from (6.1). Because p does
not divide r_p, its p-primary part and prime-to-p part separate:

\[
\gcd(r_p p^j,t)=\gcd(r_p,t)p^{\min(j,v_p(t))}.
\]

The exponent difference is max(e-c_p-v_p(t),0), giving (6.2).

**Theorem 6.2, singular basis.** Suppose p divides F_t. Let lambda be the
nonzero scalar a_t modulo p, and let delta be its multiplicative order.
Then delta is in {1,2,4} and, for every e>=1,

\[
\boxed{\tau_t(p^e)=\delta p^e.}\tag{6.3}
\]

*Proof.* The original element u reduces to lambda; its norm gives
lambda^2=nu_t, so delta divides four and is prime to p. For every positive n,
(5.2) and the Fibonacci valuation theorem give the exact cancellation

\[
v_p(U^{(t)}_n)=v_p(F_{tn})-v_p(F_t)=v_p(n).\tag{6.4}
\]

A return modulo p^e therefore requires p^e|n. Modulo p the characteristic
polynomial of B_t is (X-lambda)^2. Thus B_t=lambda*I+D with D^2=0, and
B_t^n=lambda^n*I whenever p|n. A return also requires delta|n.

Conversely assume delta*p^e divides n. Equation (6.4) gives U_n^(t)=0 modulo
p^e. The companion-power identity makes B_t^n a scalar matrix cI. Its
reduction modulo p is lambda^n I=I, so c=1 modulo p. Moreover
c^2=det(B_t)^n=nu_t^n=1: if nu_t=-1, then delta=4 and n is even.
The factor c+1 is a unit modulo the odd prime power;
from (c-1)(c+1)=0 it follows that c=1 modulo p^e. Thus the matrix returns.
The two necessary divisibilities were coprime, which also proves minimality.
This proves (6.3), including the odd-t case delta=4.

**Corollary 6.3, complete plateau criterion.** For every t>=1 and p!=2,5 prime,

\[
\boxed{
\tau_t(p^2)=\tau_t(p)
\iff
p\nmid F_t\ \land\
\bigl(p\text{ is a classical WSS prime}\ \lor\ p\mid t\bigr).
}\tag{6.5}
\]

The singular case never has a plateau. In the invertible case, (6.2) shows
that a plateau occurs exactly when c_p+v_p(t)>=2. This is the stated
alternative because c_p>=1.

This formula describes two distinct ways in which a proposed golden-power
argument can fail to isolate the target. At p|t, pre-powering itself extends
the plateau. At p|F_t, the companion change of basis is singular, and dividing
by F_t cancels the unknown initial depth altogether. Only when p does not
divide t*F_t does the derived plateau coincide with the classical WSS
condition. Fixed t has only finitely many exceptional primes of these two
types; outside them the equivalence is exact, but it supplies no new
cross-prime constraint on c_p.

For example t=p=3 gives L_t=4 and F_t=2. The companion periods modulo 3 and
9 are both 8, although the original Fibonacci periods are 8 and 24. This
is a valid generalized-sequence plateau and no classical WSS witness.
For t=8, p=3, the singular basis produces tau_8(3^e)=3^e, consistent with
the a=47 line already considered separately in PR #7709.

## 7. Prior-art scope and the remaining WSS target

The exact Conjecture 6.3 wording was checked in the primary arXiv v2 and the
publisher's retrieved 2025 text. The OEIS A175286 entry was checked separately
for the recurrence-period convention. Searches of the title, authors,
conjecture number, Jacobsthal fixed points, modular periods and multiplicative
order did not locate an earlier proof of the fixed-point assertion in the
sources returned. GitHub searches found the existing A175286 LODA program,
which computes terms, and old digit-gas Jacobsthal specializations in this
repository; neither is a proof of the classification. The general period
formula is not independently claimed new. Unindexed work and priority remain
unverified, and no claim of OEIS editorial acceptance is made.

A separate current WSS lead was checked and is explicitly not counted as new:
Ross, Shen and Cai [4], Corollary 5.1, already prove that absence of classical
WSS primes is equivalent to squarefreeness of all the Fibonacci multiplicative
Mobius duals except at index six. That reformulation cannot be repackaged as a
new resolution. Their paper retains the unknown initial valuation, just as
(6.1) does.

The current work establishes no prime with c_p>=2 and no theorem that c_p=1
for every prime. Theorem (6.5) determines exactly what an attempt using genuine
golden powers can establish without an additional arithmetic input. The
Jacobsthal fixed-point proof closes a neighboring external target with explicit
semantics; it is not a proof of WSS existence.

## References

[1] Brennan Benfield and Oliver Lippard. *Fixed Points of K-Fibonacci Sequences*.
Fibonacci Quarterly, 2025, pp. 259-274. DOI: 10.1080/00150517.2025.2491986.
Conjecture 6.3; arXiv:2404.08194v2, July 29, 2024.
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

The complete ordinary proofs are Sections 2-6. The Lean companion in this
submission covers the source recurrence, the exact all-tail criterion (2.2),
and the absence of pure periods at even moduli. The totient classification
(4.1) and the golden-power formulas (6.2)-(6.5) are ordinary mathematical
proofs, not new Lean/kernel-certified declarations. No Lean/lake executable is
available in this environment; the new script was not elaborated. No custom
axiom, admitted proof, resolution marker, freeze, CI pass or independent
multi-model review is claimed.
