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
