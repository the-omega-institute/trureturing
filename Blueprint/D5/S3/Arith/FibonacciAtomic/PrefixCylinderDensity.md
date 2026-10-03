# Natural Density of Canonical Fibonacci Prefixes

## Abstract

Fixed Zeckendorf prefixes have bounded counting discrepancy and positive density.

**Definition 1.1 (Legal occupied prefix indices).**

$$\operatorname{LegalPrefix}\left(m, w\right)\Leftrightarrow\operatorname{IsZeckendorfRep}\left(w\right)\land\forall k\in w,k<m+2$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.LegalPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A prefix of length m is represented by its descending list w of occupied Fibonacci indices. All indices are at least two, successive occupied indices differ by at least two, and every index is less than m+2. Index j+2 is the low-first binary digit j. The length retains high zero digits, including the empty prefix at m=0.

**Definition 1.2 (The seam-adjusted free tail depth).**

$$h = m+sigma$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.seamDepth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write sigma=1 when m+1 belongs to w, and sigma=0 otherwise; h=m+sigma. Thus an occupied final prefix digit forces one extra zero before the free tail. The value of the fixed prefix is V=sum over k in w of F_k.

**Definition 1.3 (The canonical integer cylinder).**

$$\operatorname{C}\left(m, w\right) = \{n\in\mathbb{N}\mid\operatorname{filter}\left(k<m+2, \operatorname{wdigits}\left(n\right)\right)=w\}$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.cylinder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C(m,w) consists of the natural integers whose canonical occupied indices below m+2 are exactly w. All higher digits are read with zero padding. The Fibonacci convention is F_0=0 and F_1=1.

**Definition 1.4 (Counting below a real cutoff).**

$$\operatorname{N}\left(m, w, X\right) = \lvert\{n\in\operatorname{C}\left(m, w\right)\mid n<X\}\rvert$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.counting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(m,w,X) counts cylinder members n with n<X, where X is any real number. The set is finite and empty when X is nonpositive.

**Theorem 1.5 (Bounded discrepancy, natural density, and refinement ratios).**

$$\forall m,w,\operatorname{LegalPrefix}\left(m, w\right)\Rightarrow\operatorname{StrictMono}\left(t\mapsto V+s^{h}(t)\right)\land\operatorname{range}\left(t\mapsto V+s^{h}(t)\right)=\operatorname{C}\left(m, w\right)\land\exists C,\forall X\ge0,\lvert\operatorname{N}\left(m, w, X\right)-\varphi^{-h}\cdot X\rvert\le C\land\lim_{X\to\infty}\frac{\operatorname{N}\left(m, w, X\right)}{X}=\varphi^{-h}\land\forall mPrime,wPrime,\operatorname{LegalExtension}\left(m, w, mPrime, wPrime\right)\Rightarrow\lim_{X\to\infty}\frac{\operatorname{N}\left(mPrime, wPrime, X\right)}{\operatorname{N}\left(m, w, X\right)}=\varphi^{h-hPrime}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every legal prefix (m,w), the map t to V+s^h(t) is strictly increasing and has image C(m,w), where s shifts every occupied Fibonacci index up by one. In particular t=0 is retained.

There is a real constant C depending only on this prefix such that, for every real X>=0, |N(m,w,X)-phi^(-h)X|<=C. As X tends to positive infinity through real cutoffs, N(m,w,X)/X tends to phi^(-h), which is positive.

For every legal longer prefix (m',w') with m<=m' and w' restricted below m+2 equal to w, its counting ratio N(m',w',X)/N(m,w,X) tends to phi^(h-h'). If m'=m+r and its last digit is tau, this exponent is -(r+tau-sigma). When r=0, tau=sigma and the ratio tends to one.

Zeckendorf uniqueness identifies the free tail after the fixed prefix and the forced seam zero are removed. The golden Beatty floor formula for s gives |s(t)-phi*t|<=1. Iteration gives |s^h(t)-phi^h*t|<=h*phi^h. The first tail index whose image reaches X is exactly the cylinder count. Its image and its predecessor bound that count within a constant of X/phi^h. Dividing by X gives the density, and dividing the two positive density limits gives the refinement ratio.

This is a result in the classical Zeckendorf and golden Beatty setting. Background on the unique nonconsecutive expansion is J. L. Brown, Jr., Zeckendorf's Theorem and Some Applications, The Fibonacci Quarterly 2 (1964), 163-168. The error bound is for each fixed prefix; it is not uniform over all prefix lengths. No composition-coordinate lifting formula or specific three-digit or six-digit weight table is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.LegalPrefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.counting`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.cylinder`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.seamDepth`
- Dependency: [D5/S1/Deficit/Displacement/GoldenSubstStartSharpness](../../../S1/Deficit/Displacement/GoldenSubstStartSharpness.md)
- Dependency: [D5/S1/Digit/GoldenZeckendorfLanguage](../../../S1/Digit/GoldenZeckendorfLanguage.md)
