---
bibkey: montgomery1978largesieve
authors: Hugh L. Montgomery
year: 1978
title: The analytic principle of the large sieve
doi: 10.1090/S0002-9904-1978-14497-8
url: https://doi.org/10.1090/S0002-9904-1978-14497-8
claim: The classical discrete large sieve supplies a weighted square-tail allowance for the actual Weil arithmetic boundary symbol after its logarithmic frequency aliases are folded; this controls an unsigned coupling budget, not all-scale positivity.
strata_touched: []
license: citation-only
triage: anchor
---

# Discrete large-sieve input for the actual arithmetic boundary

The published input is Selberg's discrete large-sieve inequality in Montgomery, *Bulletin of the American Mathematical Society* **84** (1978), 547–567, §7, Theorem 3, printed p.559, with the finite-dimensional duality of §4, Lemma 2. The exact theorem locator and its normalization were supplied by an external source review; the publisher metadata was independently checked, but the original article's full text was not retrieved locally. The application below is paper mathematics, without a new Lean large-sieve theorem, an originality claim, or an independent audit of the source's proof.

For a finite set of frequencies separated by at least $\delta>0$ modulo one, arbitrary complex coefficients $a_\theta$, and $H\ge1$ consecutive integer samples, the dual form is

$$
\sum_{m=U+1}^{U+H}\left|\sum_\theta a_\theta e^{2\pi i m\theta}\right|^2
\le(H-1+\delta^{-1})\sum_\theta|a_\theta|^2.
\tag{1}
$$

Rational frequencies, independent prime phases, and RH are not hypotheses. The estimate is uniform in the initial sample $U$ and the sample count $H$.

## Exact aliases of the existing prime symbol

Use the [existing arithmetic boundary symbol](../../D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.lean). For an **integer** $c\ge2$, put $L=\log c$, $w_j=\Lambda(j)/\sqrt j$, and

$$
P_c(m)=\sum_{2\le j<c}w_j\sin\left(\frac{2\pi m\log j}{L}\right).
$$

Its positive and negative exponential frequencies are $\pm\log j/L$ modulo one. Same-sign frequencies have no distinct-label collision; opposite signs collide exactly when $jk=c$. Combine these coefficients before applying (1). The resulting coefficient energy is

$$
E(c)=\frac12\sum_{j<c}\frac{\Lambda(j)^2}{j}
-\frac12\sum_{\substack{j,k<c\\jk=c}}\frac{\Lambda(j)\Lambda(k)}{\sqrt{jk}}\ge0.
\tag{2}
$$

The second sum is ordered and includes $j=k$. If $j^2=c$, its sine is zero on every integer mode; its two contributions in (2) cancel. Thus deleting the collision term is not the exact folded energy. Its omission would give a larger valid coefficient allowance if folding were still performed, but applying a separated-frequency theorem to the original colliding list would be invalid.

Distinct folded frequencies have circular separation at least

$$
\delta_c=\frac{\log(1+1/c)}{\log c},\qquad
D_c=\delta_c^{-1}\le(c+1)\log c.
\tag{3}
$$

For same-sign labels $j>k$, the two circular gaps, multiplied by $L$, are $\log(j/k)$ and $\log(ck/j)$; integrality bounds both below by $\log(1+1/c)$. For opposite signs, set $t=jk$. After removing $t=c$, the relevant gaps are the minimum of $|\log(t/c)|$, $\log t$, and $\log(c^2/t)$. The integer gap from $c$, together with $4\le t\le(c-1)^2$, proves the same bound. Removing zero folded coefficients cannot reduce separation. For arbitrary real cutoffs, the integer-gap argument from $jk$ to $c$ is unavailable.

For the integer FIB support schedule $c_0=c_1=3$, $c_{r+2}=c_{r+1}c_r$, the exact powers $c_r=3^{F_{r+1}}$ preserve this separation input. For every integer $a\ge1$, their alias correction is

$$
E(3^a)=\frac12\sum_{j<3^a}\frac{\Lambda(j)^2}{j}
-\frac{(a-1)(\log3)^2}{2\,3^{a/2}}.
\tag{4}
$$

Only ordered pairs of positive powers of three contribute to the second sum. The support recurrence is parameter matching with the existing FIB construction, not a new positivity theorem.

## Weighted infinite tails

Let $M\ge1$ be an integer and $p>1$. Write $Z_p(M)=\sum_{m>M}m^{-p}$. Equation (1) gives

$$
A_H:=\sum_{m=M+1}^{M+H}|P_c(m)|^2\le E(c)(H+D_c-1).
$$

Discrete summation by parts, with its terminal term vanishing since $A_H=O(H)$, gives the simultaneous-parameter bound

$$
\sum_{m>M}\frac{|P_c(m)|^2}{m^p}
\le E(c)\left[Z_p(M)+\frac{D_c-1}{(M+1)^p}\right]
\le E(c)\left[\frac1{(p-1)M^{p-1}}+\frac{D_c}{M^p}\right].
\tag{5}
$$

For $c=2$, the prime polynomial is zero and (5) is trivial. For $c\ge3$, $D_c>1$; this also validates replacing $Z_p$ by its integral upper bound in the displayed direction.

The existing actual symbol includes the pole and the infinite Gamma series, in addition to $P_c$. Reuse its Gamma allowance $2$ and the nonzero-mode pole allowance $K(c)/|m|$, where

$$
K(c)=\frac{L(\cosh(L/2)-1)}\pi.
$$

For $q=1,2$, put $S_{2q}(c,M)=\sum_{m>M}s(c,m)^2/m^{2q}$. Applying $|s|^2\le2|P_c|^2+2(2+K/m)^2$ to the **same** symbol gives

$$
S_{2q}(c,M)\le F_q(c,M):=
\frac{2E(c)+8}{(2q-1)M^{2q-1}}
+\frac{2E(c)D_c}{M^{2q}}
+\frac{8K(c)}{2qM^{2q}}
+\frac{2K(c)^2}{(2q+1)M^{2q+1}}.
\tag{6}
$$

The weighted $\ell^2$ triangle inequality also gives the valid alternative

$$
S_{2q}(c,M)\le
\left[
\sqrt{E(c)\left(Z_{2q}(M)+\frac{D_c-1}{(M+1)^{2q}}\right)}
+2\sqrt{Z_{2q}(M)}+K(c)\sqrt{Z_{2q+2}(M)}
\right]^2.
\tag{7}
$$

No ordering between (6) and (7) is presumed. Each is an unsigned upper bound.

The already proved sup allowance $B(c)=2\cosh(L/2)+\sum_{j<c}w_j$ remains available. Define

$$
U_q(c,M)=\min\left\{F_q(c,M),\frac{B(c)^2}{(2q-1)M^{2q-1}}\right\}.
\tag{8}
$$

Classical Chebyshev estimates and partial summation give $E(c)=O(\log^2c)$, $B(c)^2=\Theta(c)$ and $K(c)=O(\sqrt c\log c)$. These published prime-weight estimates are reused. Consequently, when $M\ge(c+1)\log c$, (6) has size $O(\log^2c/M^{2q-1})$, while the corresponding sup allowance has size $\Theta(c/M^{2q-1})$. These statements keep both growing parameters; they are not limits at fixed $c$.

## The existing second jet keeps four moments

Reuse the [second exterior jet and remainder](../../D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingSecondJet.lean) and its [actual reflection-paired Gram identity](../../D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram.lean). For the same finite vector $v$ supported on $|n|\le N$, retain

$$
A_0=\sum v_n,\quad B_0=\sum s(c,n)v_n,\quad
A_1=\sum nv_n,\quad B_1=\sum ns(c,n)v_n.
$$

The actual second jet is

$$
J_2(m)=\frac{B_0-s(c,m)A_0}{\pi m}
+\frac{B_1-s(c,m)A_1}{\pi m^2}.
$$

With $T=\sum_{m>M}s(c,m)/m^3$, its exact positive-mode Gram consists of the two blocks

$$
\begin{pmatrix}S_2&-T\\-T&Z_4\end{pmatrix}
\quad\text{on }(A_0,B_1),\qquad
\begin{pmatrix}Z_2&-T\\-T&S_4\end{pmatrix}
\quad\text{on }(B_0,A_1),
\tag{9}
$$

with the common prefactor $2/\pi^2$. The arguments of each $S_p$ and $Z_p$ are $(c,M)$ and $M$, respectively. All sums converge by the existing symbol budget. The same signed cross moment occurs in both blocks; separately optimizing scalar cross terms would not preserve the actual common realization.

One valid conservative joint majorant follows by applying $|u+v|^2\le2|u|^2+2|v|^2$ to the two full squares in the paired identity:

$$
\sum_{|m|>M}|J_2(m)|^2\le\mathcal J_{\rm new}(v):=
\frac4{\pi^2}\left[
U_1|A_0|^2+\frac{|B_1|^2}{3M^3}
+\frac{|B_0|^2}{M}+U_2|A_1|^2
\right].
\tag{10}
$$

Here no moment or coefficient is removed. Compare (10) with the **same Young majorant** $\mathcal J_{\rm old}$, replacing $U_1$ by $B(c)^2/M$ and $U_2$ by $B(c)^2/(3M^3)$. Their difference is nonnegative for every vector. This does not assert that (10) improves an already sharper certificate retaining the signed cross term in (9). The $B_0$ and $B_1$ directions are unchanged, so it also does not give a uniform strict multiplicative saving for every individual vector.

For integer $M>N$, put $\kappa=1-N/(M+1)>0$ and $U(v)=\sum|v_n|$. The existing second-jet remainder $R_m=C_m(v)-J_2(m)$, with the **actual** coupling column

$$
C_m(v)=\sum_{|n|\le N}\frac{s(c,n)-s(c,m)}{\pi(m-n)}v_n,
$$

has the square-summed allowance

$$
\sum_{|m|>M}|R_m|^2\le
\mathcal R_2(v):=
\frac{8B(c)^2N^4U(v)^2}{\pi^2\kappa^2}Z_6(M)
\le\frac{8B(c)^2N^4U(v)^2}{5\pi^2\kappa^2M^5}.
\tag{11}
$$

This is a summation of the existing pointwise theorem, not a new jet approximation. For any fixed $\varepsilon>0$, the whole actual column obeys

$$
\sum_{|m|>M}|C_m(v)|^2\le
(1+\varepsilon)\mathcal J_{\rm new}(v)
+(1+\varepsilon^{-1})\mathcal R_2(v).
\tag{12}
$$

The old/new comparison uses the same $N,M,\varepsilon$, remainder, and Schur denominator. Every middle mode $N<|m|\le M$ stays in the independently retained shell. Moving $M$ outwards does not delete that shell or its coupling.

For the actual vector supported only at $n=0$, $s(c,0)=0$ makes $B_0=A_1=B_1=0$ and $R_m=0$. Its exact exterior energy is $2S_2/\pi^2$. Thus the scalar supplier has a genuine coupling consumer, while this one direction supplies no full Schur positivity conclusion.

## A growth regime and its limitations

At $N=\lceil\log c\rceil$, $M=\lceil(c+1)\log c\rceil$, the new $A_0$ coefficient is smaller than the old one by order $\log^2c/c$ for large $c$. The second-jet remainder operator allowance is $O(c^{-4})$ since $U(v)^2\le(2N+1)\|v\|_2^2$. This comparison concerns the far coupling. A positive exterior Schur margin at these small interior cutoffs has not been supplied.

A deliberately conservative all-vector regime is

$$
N=\lceil e^c\rceil,\qquad M=N^2.
\tag{13}
$$

Apply the same large-sieve input to $1\le n\le N$. With $W(c)=\sum_{j<c}w_j$ and $H_2(N)=\sum_{n=1}^Nn^{-2}$,

$$
\sum_{|n|\le N}s(c,n)^2\le
2\left[\sqrt{E(c)(N-1+D_c)}+2\sqrt N+K(c)\sqrt{H_2(N)}\right]^2
=O(N\log^2c).
\tag{14}
$$

Also $\sum n^2s(c,n)^2\le N^2\sum s(c,n)^2$. The four actual moment functionals in (10) therefore give

$$
\|\mathcal J_{\rm new}\|=O(\log^2c/N),\qquad
\|\mathcal R_2\|=O(c/N^5).
\tag{15}
$$

The same sup-based Young majorant has a constant-vector direction of order $c/N$, by oddness of $s(c,n)$. Hence the new all-vector upper allowance improves that named comparison, and the unchanged remainder does not erase the saving. Equation (15) is not a claim that the exact coupling operator has either asymptotic size or a lower bound.

The [existing infinite-complement leakage bound](../../D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage.lean) can also be reused in (13). Under its existing Fourier/Plancherel identification and the actual Weil-form domain bridge, at most $\eta=4/(3\pi^2)$ of an exterior unit vector's Fourier mass lies in $|t|\le\pi N/(2L)$. In the source normalization, let

$$
h(t)=\Re\operatorname{digamma}(1/4+it/2)-\log\pi,\qquad
h_0=h(0)=-\gamma-\pi/2-3\log2-\log\pi.
$$

Its classical partial-fraction expansion gives $h(t)\ge h_0$. The scalar digamma lower estimate $h(t)\ge\log(t/(2\pi))-1/t$ for $t\ge15/4$ is stated in [Zhu, arXiv:2608.24827v2](https://arxiv.org/pdf/2608.24827v2), Lemma 3.1; the [existing localization source note](../Weil/suzuki2026screw.md) distinguishes its scalar inputs from its fixed-window positivity claims. The prime form retains its worst-case allowance $2W(c)$, and the pole form has absolute allowance $4\sinh(L/2)$ on the full complex space. The latter follows by Cauchy–Schwarz on its two exponential moments; no pole positivity is assumed.

Consequently an exterior lower allowance, when $\pi N/(2L)\ge15/4$, is

$$
d(c,N)=(1-\eta)\left[\log\frac{N}{4L}-\frac{2L}{\pi N}\right]
+\eta h_0-2W(c)-4\sinh(L/2).
\tag{16}
$$

In (13), $d(c,N)=(1-\eta)c-O(\sqrt c+\log\log c)>0$ for all sufficiently large $c$. This is a lower bound on the **exterior block**, not on the lowest eigenvalue of the whole Weil form. It makes the same Schur denominator available: the old far allowance divided by $d$ is of order $1/N$, whereas the new allowance is $O(\log^2c/(cN))$. All middle modes and the retained finite Schur complement still require their actual arithmetic estimates. The exponential interior size in (13) is not an efficient finite certification scheme.

## A recent weighted sieve does not supply the missing sign

[Olivier Ramaré, *The weighted large sieve through Parseval*, arXiv:2609.25885v1](https://arxiv.org/pdf/2609.25885v1), submitted 22 September 2026, was inspected in the primary PDF and HTML. Its Theorem 1.3 bounds a sequence supported on a **consistent multiplicative system of allowed residue classes satisfying the Johnsen–Gallagher condition**. Theorem 1.4 adds regularity and sieve-range assumptions. These hypotheses and its arithmetical denominator are not the arbitrary logarithmic-frequency input in (1). No matching system for the actual coupled coefficient family has been established, so its improved constants cannot simply be inserted into (5). The paper supplies a distinct published research direction, not a verified replacement for this source application.

The remaining RH obligation is the sign of the complete retained Schur complement, or an independently established nonnegative support-decomposition remainder for the [existing golden positivity induction](../../D5/S3/Weil/TestFunctions/GoldenPositivityInduction.lean). An unsigned square-tail estimate does not prove either condition. The [fixed-window full Gram certificate](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md) is reused rather than recomputed; no extension of its support window, all-scale positivity, or RH proof is claimed here. The integral/form identifications, the large-sieve application, the infinite Gram summation and the exterior lower allowance in this note remain paper-level bridges, separate from the cited Lean modules' checked statements.
