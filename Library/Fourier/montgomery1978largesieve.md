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

For a finite set of frequencies separated by at least $0<\delta\le1$ modulo one, arbitrary complex coefficients $a_\theta$, and $H\ge1$ consecutive integer samples, the dual form is

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

For the actual vector supported only at $n=0$, $s(c,0)=0$ makes $B_0=A_1=B_1=0$ and $R_m=0$. Its exact exterior energy is $2|v_0|^2S_2/\pi^2$. Thus the scalar supplier has a genuine coupling consumer, while this one direction supplies no full Schur positivity conclusion.

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

## The shared signed cross from existing Fourier data

For the same integer $c\ge3$, $M\ge1$, actual symbol $s(c,m)$ and second jet, put

$$
T(c,M)=\sum_{m>M}\frac{s(c,m)}{m^3},\qquad
a=\frac{L}{4\pi},\qquad
H(c)=\sum_{2\le j<c}\frac{w_j}{|\sin(\pi\log j/L)|}.
\tag{17}
$$

All prime frequencies lie strictly between zero and one, so the denominators are nonzero. The existing symbol envelope proves absolute convergence of $T$. No phase independence is assumed.

The classical cubic sine Fourier identity is already supplied by `hasSum_one_div_nat_pow_mul_sin`, $k=1$, in [pinned Mathlib's ZetaValues](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ZetaValues.lean). Its direct real application was compiled transiently; no new named declaration is retained. With $B_3(u)=u^3-3u^2/2+u/2$, this gives the actual prime tail by a finite expression:

$$
Q_3(c,M)=\sum_{2\le j<c}w_j\left[
\frac{2\pi^3}{3}B_3\!\left(\frac{\log j}{L}\right)
-\sum_{m=1}^M\frac{\sin(2\pi m\log j/L)}{m^3}\right]
=\sum_{m>M}\frac{P_c(m)}{m^3}.
\tag{18}
$$

This is an application of an existing theorem. The naive finite evaluation costs one sine sum per prime-power label and can subtract nearly equal quantities; it does not supply an efficient or numerically certified algorithm at growing exponential cutoffs. Alternatively, geometric summation bounds every consecutive sum of $e^{2\pi i m u}$ by $1/|\sin(\pi u)|$. Summation by parts with decreasing $m^{-3}$ then gives the source-level envelope

$$
|Q_3(c,M)|\le\frac{H(c)}{(M+1)^3}.
\tag{19}
$$

The actual positive-mode pole is $p_m=Km/(m^2+a^2)$. Hence

$$
0\le KZ_4(M)-\sum_{m>M}\frac{p_m}{m^3}
\le Ka^2Z_6(M).
\tag{20}
$$

For the same Gamma series, write $b_j=2j+1/2$ and
$G_L(\omega)=\sum_{j\ge0}\omega(1-e^{-b_jL})/(b_j^2+\omega^2)$ for $\omega>0$.
The existing upper envelope $G_L(\omega)\le\pi/4+1/\omega$ is reused. Its needed lower counterpart follows from decreasing-series/integral comparison:

$$
\begin{aligned}
\frac\pi4-\frac12\arctan\frac1{2\omega}
&\le\sum_{j\ge0}\frac\omega{b_j^2+\omega^2}
\le\frac\pi4+\frac1\omega,\\
\sum_{j\ge0}\frac{\omega e^{-b_jL}}{b_j^2+\omega^2}
&\le\frac1\omega\frac{c^{-1/2}}{1-c^{-2}}.
\end{aligned}
$$

Since $c\ge3$, $1/4+c^{-1/2}/(1-c^{-2})\le1/4+9/(8\sqrt3)<1$. Thus the two-sided allowance for the **actual** damped Gamma symbol is

$$
\left|G_L(\omega)-\frac\pi4\right|\le\frac1\omega.
\tag{21}
$$

Define $g=LZ_4(M)/(2\pi)$ and $r=Ka^2Z_6(M)$. Combining (18), (20) and (21), with the actual sign $s=-P-G-p$, yields

$$
t_B-g\le T(c,M)\le t_B+g+r,
\qquad t_B=-Q_3(c,M)-\frac\pi4Z_3(M)-KZ_4(M).
\tag{22}
$$

Equivalently, use center $t_*=t_B+r/2$ and radius $\epsilon_*=g+r/2$. A version without evaluating the prime tail is

$$
|T(c,M)-t_0|\le\epsilon,
\quad t_0=-\frac\pi4Z_3(M)-KZ_4(M),\quad
\epsilon=\frac{H(c)}{(M+1)^3}+g+r.
\tag{23}
$$

These are paper-level estimates for the existing symbol, rather than new Lean tail theorems. Only the quoted upstream Fourier identity's direct application has the stated compilation evidence.

### An elementary uniform sign regime

No prime-distribution estimate is needed for a conservative $H$ bound. Use $\Lambda(j)\le\log j\le L$ and $\sin(\pi u)\ge2\min(u,1-u)$. For $j\le c/2$, both logarithms in the minimum are at least $\log2$, and $\sum_{j<c}j^{-1/2}\le2\sqrt c$. For $j>c/2$, use $\log(c/j)\ge(c-j)/c$, $\sqrt j\ge\sqrt{c/2}$ and the harmonic-sum bound. Together these give

$$
H(c)\le\frac{L^2\sqrt c}{\log2}
+\sqrt{c/2}\,L^2(1+L).
\tag{24}
$$

Retaining the nonnegative pole only helps the upper sign estimate. Integral comparisons $Z_3(M)\ge1/[2(M+1)^2]$ and $Z_4(M)\le1/(3M^3)$ give

$$
T(c,M)\le-\frac\pi{8(M+1)^2}
+\frac{H(c)}{(M+1)^3}+\frac{L}{6\pi M^3}.
\tag{25}
$$

For every integer $c\ge100000$ and integer $M\ge c\log c$, the right side is negative. Indeed, after multiplication by $(M+1)^2$, the two positive terms are at most

$$
\frac{L}{\log2\sqrt c}+\frac{L(1+L)}{\sqrt{2c}}+\frac1c.
$$

Each term decreases in this range; the second has derivative sign $1+3L/2-L^2/2<0$. At $c=100000$, use $L<11513/1000$, $\log2>69/100$, $\sqrt c>316$, $\sqrt2>707/500$ and $\pi>157/50$. The sufficient comparison is the exact rational inequality

$$
\frac{11513/1000}{316(69/100)}
+\frac{(11513/1000)(1+11513/1000)}{316(707/500)}
+\frac1{100000}
=\frac{289213404239}{770771400000}
<\frac{157}{400}<\frac\pi8.
\tag{26}
$$

The logarithmic bounds can be checked from the exponential Taylor series: its positive sum through degree 80 at $11513/1000$ exceeds $100000$, while the sum through degree 10 at $69/100$ plus its geometric tail bound is below 2. The square-root comparisons follow by squaring. The classical Machin identity and alternating arctangent bounds give $\pi>16(1/5-1/(3\cdot5^3))-4/239=281476/89625>157/50$. These rational comparisons were evaluated exactly; the all-parameter conclusion also uses the displayed paper monotonicity and tail arguments. It is not a Lean-certified sign theorem or a sign conclusion for the entire Weil form.

### One cross interval for both Gram blocks

For either valid center-radius pair $(t,\varepsilon)$ from (22) or (23), use the normalized variables $z_1=(A_0,B_1/M)$ and $z_2=(B_0,A_1/M)$. Both exact blocks then have the common off-diagonal $-MT$. The two simultaneous upper matrices are

$$
\widetilde G_1=
\begin{pmatrix}U_1&-Mt\\-Mt&M^2Z_4\end{pmatrix}
+M\varepsilon I,
\qquad
\widetilde G_2=
\begin{pmatrix}Z_2&-Mt\\-Mt&M^2U_2\end{pmatrix}
+M\varepsilon I.
\tag{27}
$$

The diagonal differences are nonnegative by (8). The remaining error matrix has off-diagonal $-M(T-t)$; its quadratic form is at most $M\varepsilon\|z\|^2$. Thus (27) jointly majorizes the **same** two exact blocks, and $2(z_1^*\widetilde G_1z_1+z_2^*\widetilde G_2z_2)/\pi^2$ is a valid second-jet energy allowance for every complex finite vector. All four moments remain. Use this whole-vector allowance alongside (10); no universal matrix ordering between the two majorants is claimed.

The unchanged second-jet remainder (11), the same Young transport (12), and every middle mode $N<|m|\le M$ remain necessary for the actual coupling. Twenty finite parameter/precision diagnostics at 45 and 65 decimal digits checked the prime-tail envelope, actual pole/Gamma normalization and 80 actual-vector jet inequalities. The numerical checks use neither directed rounding nor an infinite-form certificate. Negative $T$ determines a cross coefficient's sign; its contribution still depends on the joint moment phases, and proves neither complete retained-Schur positivity nor an induction remainder sign. The remaining RH obligation is unchanged.

### A common endpoint allowance without extra matrix-radius loss

Both Cauchy–Schwarz inequalities apply to the same actual $T$, so define

$$
\tau=\min\{\sqrt{U_1Z_4},\sqrt{Z_2U_2}\},\qquad
I=[t_B-g,t_B+g+r]\cap[-\tau,\tau]=[\ell,u].
\tag{28}
$$

This interval is nonempty because it contains $T$. The symmetric interval in (23) can replace the first interval if the finite prime expression is not evaluated. Write

$$
D(v)=U_1|A_0|^2+Z_4|B_1|^2+Z_2|B_0|^2+U_2|A_1|^2,
\quad
X(v)=\Re(\overline{A_0}B_1+\overline{B_0}A_1).
$$

With $t_I=(\ell+u)/2$ and $e_I=(u-\ell)/2$, the whole second jet has the allowance

$$
\sum_{|m|>M}|J_2(m)|^2\le
\mathcal J_I(v):=\frac2{\pi^2}
\left[D(v)-2t_IX(v)+2e_I|X(v)|\right]
=\frac2{\pi^2}\max_{t\in\{\ell,u\}}\{D(v)-2tX(v)\}.
\tag{29}
$$

Each endpoint is used simultaneously in both Gram blocks. The maximum bounds one identified arithmetic quantity; it does not assert that either endpoint is attained by that arithmetic symbol. Replacing $|X(v)|$ by the sum of the two individual absolute cross terms would discard a possible cancellation between the blocks.

For every $t\in I$, $|t|\le\sqrt{U_1Z_4}$ and $|t|\le\sqrt{Z_2U_2}$. Thus each endpoint block is positive semidefinite and its quadratic form is at most twice its diagonal form. Consequently,

$$
\mathcal J_I(v)\le\frac4{\pi^2}D(v)\le\mathcal J_{\rm new}(v).
\tag{30}
$$

This is a uniform comparison of the named upper allowances. It does not supply a strict saving for every vector or reduce the actual retained operator to four coordinates.

The sign of the cross alone cannot determine a favorable contribution for all actual vectors. For $c=3$ and $N=2$, $1/2<\log2/\log3<3/4$ implies $P_3(2)>0$, and the positive pole and Gamma terms give $s(3,2)<0$. Set $v_{-2}=v_2=1$, with either $v_0=-1$ or $v_0=-3$ and all other coefficients zero. Both vectors have $B_0=A_1=0$ and $B_1=4s(3,2)$, but their respective $X$ values are $4s(3,2)<0$ and $-4s(3,2)>0$. These are two realized moment configurations for the same symbol.

At $M=200$, the coarse bounds $H(3)<40$ and $L/(2\pi)<1$ in (24), together with $Z_4\le Z_3/(M+1)$, give $T(3,200)<0$: its upper coefficient relative to $Z_3$ is less than $-\pi/4+81/201<0$. Therefore $-2TX$ decreases the energy for one of these vectors and increases it for the other. The general change of cross has an error matrix with eigenvalues of opposite signs; a retained-Schur argument must handle both common endpoints or establish a further constraint on the actual moment image.

### A uniform reduction of the named jet allowance

For $c\ge100000$ and integer $M\ge c\log c$, use the exact-Fourier interval (22) in (28). Let $\mathcal J_*$ be the normalized quadratic allowance (27) with center $t_*=t_B+r/2$ and radius $\epsilon_*=g+r/2$. Then

$$
\mathcal J_I(v)\le\mathcal J_*(v)
\le\frac45\mathcal J_{\rm new}(v)
\qquad\text{for every finite complex coefficient vector }v.
\tag{31}
$$

The first inequality follows because every endpoint lies in $[t_*-\epsilon_*,t_*+\epsilon_*]$ and $2|X(v)|\le M(\|z_1\|^2+\|z_2\|^2)$. The second is a comparison of the same two moment matrices. Its constants can be checked without evaluating the growing prime sum.

The decreasing envelope in (26) is below $19/50$, so $H(c)/M<19/50$. Also $K/M\le1/(2\pi\sqrt c)$ and $a/M\le1/(4\pi c)$. Integral upper bounds for $Z_3,Z_4,Z_6$ give

$$
M^2|t_*|<\frac12+\frac{19}{50}+\frac1{1000}+\frac1{1000}<\frac9{10},
\qquad
M^2\epsilon_*\le\frac1{6c}+\frac1{320c^{5/2}}<\frac1{1000}.
\tag{32}
$$

Here $M^2r/2\le1/(320c^{5/2})$ and $KM^2Z_4\le K/(3M)<1/1000$. Since $E\ge0$, $F_1\ge8/M$ and $F_2\ge8/(3M^3)$. Since $B^2\ge c+2\ge8$, taking the minimum in (8) still gives $U_1\ge8/M$ and $M^2U_2\ge8/(3M)$. These are lower bounds on the chosen **allowance coefficients**, not lower bounds on the actual $S_2$ or $S_4$.

Before the common factor $2/\pi^2$, the Young matrices on $z_1,z_2$ are $Y_1=\operatorname{diag}(2U_1,2/(3M))$ and $Y_2=\operatorname{diag}(2/M,2M^2U_2)$. The differences $(4/5)Y_i-\widetilde G_i$ have diagonal lower bounds

$$
\left(\frac{4799}{1000M},\frac{199}{1000M}\right),
\qquad
\left(\frac{599}{1000M},\frac{1599}{1000M}\right),
$$

and off-diagonal modulus below $9/(10M)$. Their diagonal products are at least $955001/(10^6M^2)$ and $957801/(10^6M^2)$, both greater than $81/(100M^2)$. The elementary two-by-two positivity criterion therefore proves the second inequality in (31). This is a paper application of the existing Fourier supplier and bounds, without a new Lean theorem or an originality claim.

If all four moments vanish, both named jet allowances are zero. The comparison gives no strict improvement in that kernel. The full actual-column allowance still adds the unchanged remainder (11), and all middle modes remain; neither the full coupling nor the retained Schur loss is asserted to shrink by a factor $4/5$.

For clarity, define $\mathcal E_{\rm mid}(v)=\sum_{N<|m|\le M}|C_m(v)|^2$. For the same $c,N,M$ and $\eta>0$,

$$
\sum_{|m|>N}|C_m(v)|^2\le
\mathcal E_{\rm mid}(v)+(1+\eta)\mathcal J_I(v)
+(1+\eta^{-1})\mathcal R_2(v).
\tag{33}
$$

When the actual exterior block has a lower bound $D_{\rm ext}\succeq d(c,N)I$ with $d(c,N)>0$, one sufficient next step for this allowance-based Schur argument is to prove that the actual retained form dominates the entire right side of (33), divided by $d(c,N)$, for every retained vector along a cofinal support exhaustion. The common endpoints, the middle shell, the remainder and the form-domain/exhaustion bridges all enter this condition. Failure of these upper allowances to fit would not refute positivity or RH. No source or estimate in this note establishes that domination. For the existing FIB schedule $c_r=3^{F_{r+1}}$, the range $c_r\ge100000$ begins at $r=6$; parameter matching supplies (31) there when $M\ge c_r\log c_r$, and supplies no additional retained-form sign.

## The existing RH route admits an even-sector consumer

The repository's `WeilTestFunction` already means an even smooth compactly supported complex function. Its [Weil-square criterion](../../D5/S3/Weil/Separator/WeilSquarePositivityCriterion.lean) proves that positivity for these tests suffices for RH; the [explicit-formula criterion](../../D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion.lean) transports the same statement to the complete pole-minus-prime-plus-Gamma expression. The existing [canonical zero data](../../D5/S3/Weil/ZeroData/UnconditionalCanonicalZeroData.lean) and [archimedean convergence theorem](../../D5/S3/Weil/Separator/ArchimedeanConvergence.lean) discharge its supplied-data and convergence parameters. Their direct exact application was compiled with only the standard `propext`, `Classical.choice` and `Quot.sound` axioms; the temporary check was removed without adding a named wrapper. Historical module comments describing zero-data existence as open do not override the canonical provider's statement.

Thus this route need not separately establish positivity for every odd test. It still needs positivity of the **complete** form for every admitted even test along a cofinal support exhaustion. The [existing cofinal layer transfer](../../D5/S3/Weil/CofinalSupport/GoldenCofinalPositivity.lean) is reusable; it supplies no layer's positivity. Identifying the Fourier coefficient space and its form domain with these tests remains the stated paper-level bridge.

In the phase-adjusted symmetric-window Fourier basis, reflection sends mode $n$ to mode $-n$. An even complex test therefore corresponds to

$$
v_{-n}=v_n,
$$

without complex conjugation. Reuse [the actual symbol's oddness and paired Gram identity](../../D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram.lean). On a symmetric retained index set this gives $B_0=A_1=0$. Substitution into (9) keeps the $(A_0,B_1)$ block, with exact second-jet energy

$$
\sum_{|m|>M}|J_2(m)|^2=
\frac2{\pi^2}\bigl(S_2|A_0|^2+Z_4|B_1|^2
-2T\Re(\overline{A_0}B_1)\bigr).
\tag{34}
$$

The same interval $I=[\ell,u]$ from (28) yields the restricted allowance

$$
\mathcal J_I^{\rm even}(v)=\frac2{\pi^2}
\max_{t\in\{\ell,u\}}
\bigl(U_1|A_0|^2+Z_4|B_1|^2
-2t\Re(\overline{A_0}B_1)\bigr).
\tag{35}
$$

This is the existing allowance's restriction to the actual even coefficient space, not a new moment estimate. The former actual-vector example with $v_{\pm2}=1$ and $v_0=-1$ or $-3$ already lies in this space and has opposite cross signs. Evenness alone therefore does not make negative $T$ favorable for every vector. Every middle mode and the full remainder (11) still enter (33).

For this even-sector Schur route, an actual exterior bound $D_{{\rm ext},{\rm even}}\succeq d_{\rm even}(c,N)I>0$ and domination by the actual retained **even** form of

$$
\frac{\mathcal E_{\rm mid}(v)+(1+\eta)\mathcal J_I^{\rm even}(v)
+(1+\eta^{-1})\mathcal R_2(v)}{d_{\rm even}(c,N)}
\tag{36}
$$

for all symmetric retained vectors are sufficient, with the same form-domain bridge and cofinal support requirement. A lower bound valid on the whole exterior space also restricts to this subspace. A positive finite even compression alone does not pay for its infinite even complement. Neither (34)–(36) nor the existing criterion supplies the missing domination.

The [Liu fixed-window source](../Weil/liu2026tailcompensation.md) gives a different retained positive-tail mechanism at half-width $17/16$. Its even restriction keeps the tail-filtered $h_0$ correction. The first new FIB half-width $\log3$ remains outside that theorem's range; importing its fixed-window matrices or constants there would require new support-dependent estimates.
