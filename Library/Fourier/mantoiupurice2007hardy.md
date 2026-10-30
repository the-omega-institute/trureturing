---
bibkey: mantoiupurice2007hardy
authors: Marius Măntoiu and Radu Purice
year: 2007
title: Hardy type inequalities with exponential weights for a class of convolution operators
doi: 10.1007/s11512-006-0035-4
url: https://projecteuclid.org/journals/arkiv-for-matematik/volume-45/issue-1/Hardy-type-inequalities-with-exponential-weights-for-a-class-of/10.1007/s11512-006-0035-4
claim: Lemma 3.1 supplies exponential integrability of inverse Fourier transforms of sufficiently many derivatives of strip-analytic symbols. Applied with one derivative to the exact Gamma symbol, it pays the bounded capped-weight commutator used in the same-source weighted null estimate. The paper does not supply that actual theta/Möbius null-source theorem, positivity, RH or Robin.
strata_touched: []
license: citation-only
triage: anchor
---

# Exponential convolution-kernel supplier for the actual Gamma weight

Măntoiu--Purice, *Hardy type inequalities with exponential weights for
a class of convolution operators*, Arkiv för Matematik **45** (2007),
83--103, DOI [10.1007/s11512-006-0035-4](https://doi.org/10.1007/s11512-006-0035-4).
The published [primary](https://projecteuclid.org/journals/arkiv-for-matematik/volume-45/issue-1/Hardy-type-inequalities-with-exponential-weights-for-a-class-of/10.1007/s11512-006-0035-4),
Notation 2.1 and Lemma 3.1, printed pp.87 and 89, are the supplier.

## Published statement and the required symbol class

For a strip-analytic symbol $\rho$, Notation 2.1's
$\mathcal O_0^s(\mathbb C_\delta^n)$ requires, uniformly on each
smaller closed strip,
$$
 |\partial^\alpha\rho(x+iy)|\le C_\alpha
 \min\{\langle x\rangle^{s-|\alpha|},\langle\rho(x+iy)\rangle\}.
$$
For $s>0$ and an integer $m>s$, Lemma 3.1 gives
$$
 \max_{|\alpha|=m}\sup_{0\le t\le1}
 \int_{\mathbb R^n}e^{t\gamma|h|}
   |(\partial^\alpha\rho)^\vee(h)|dh<\infty
 \qquad(0<\gamma<\delta).
$$
This is a `literature-attested` kernel lemma. Its use does not require
the regular-energy hypothesis of Theorem 2.4. No new general kernel
or Agmon theorem is asserted.

## Actual-symbol map and remaining source obligations

The [weighted null application](../Weil/platttrudgian2021rh.md#weighted-null-estimates-in-the-actual-theta-coordinate),
VHN5--VHN6, uses $n=1$, $\delta=5/4$, $0<s<1$ and $m=1$.
Digamma recurrence shifts its first surviving pole from the apparent
quarter-width to $5/4$, retaining the original rational factor.
The resulting Gamma symbol has logarithmic growth and derivatives
of order $O(\langle\Re z\rangle^{-j})$ on smaller closed strips,
so it satisfies the published symbol-class conditions. The lemma
gives $e^{\gamma|h|}(p')^\vee(h)\in L^1$; the commutator difference
cancels the off-diagonal factor $1/h$ in the kernel of $p(D)$.

The same application separately proves actual theta-image domain
membership, all-dilation mixed-moment coercivity and the complete
mixed arithmetic debit bound. These are source-relative interfaces,
not conclusions of the published lemma. In particular the original
moment is nonlocal in the Gamma coordinate, so no scalar-potential
eigenfunction-decay theorem is substituted. The resulting estimate
has no Lean/kernel certification, literature-priority claim or
positivity conclusion for the complete energy.
