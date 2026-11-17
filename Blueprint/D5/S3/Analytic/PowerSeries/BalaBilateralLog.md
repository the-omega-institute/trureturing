# Bala's bilateral logarithm identity

## Abstract

The two variable-exponent tails are absolutely convergent throughout the separate complex unit disks and their sum is the principal negative logarithm.

**Definition 1.1 (The positive source tail).**

$$\forall x \in \mathbb{C},\; \forall a \in \mathbb{C},\; \forall k \in \mathbb{N},\; \operatorname{positive}\left(x, a, k\right) = \frac{\left(x - a^{k + 1}\right)^{k + 1}}{k + 1}$$

*Formalization.* `D5/S3/Analytic/PowerSeries/BalaBilateralLog.positive` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2025). *The bilateral logarithm conjecture in OEIS A292179 and A292178*. URL: <https://oeis.org/A292179>.

*Commentary.*

The natural index k starts at zero; the source index is m=k+1. Both parameters are arbitrary complex numbers. This polynomial expression and its positive integer divisor define p_m independently of a proposed sum.

**Definition 1.2 (The regular negative tail).**

$$\forall x \in \mathbb{C},\; \forall a \in \mathbb{C},\; \forall k \in \mathbb{N},\; \operatorname{negative}\left(x, a, k\right) = \frac{\left(0 - 1\right)^{k + 2} \cdot a^{\left(k + 1\right) \cdot \left(k + 1\right)}}{\left(k + 1\right) \cdot \left(1 - x \cdot a^{k + 1}\right)^{k + 1}}$$

*Formalization.* `D5/S3/Analytic/PowerSeries/BalaBilateralLog.negative` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2025). *The bilateral logarithm conjecture in OEIS A292179 and A292178*. URL: <https://oeis.org/A292179>.

*Commentary.*

This is q_m=(-1)^(m+1)a^(m*m)/(m(1-x*a^m)^m), with m=k+1. The theorem establishes nonzero denominators on the separate unit disks. This regular expression is defined at a=0; it is distinct from the raw negative-power expression.

**Definition 1.3 (The sum of the two independently defined tails).**

$$\forall x \in \mathbb{C},\; \forall a \in \mathbb{C},\; \operatorname{regularSum}\left(x, a\right) = \operatorname{tsum}\left(\operatorname{positive}\left(x, a\right)\right) + \operatorname{tsum}\left(\operatorname{negative}\left(x, a\right)\right)$$

*Formalization.* `D5/S3/Analytic/PowerSeries/BalaBilateralLog.regularSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2025). *The bilateral logarithm conjecture in OEIS A292179 and A292178*. URL: <https://oeis.org/A292179>.

*Commentary.*

F(x,a) is the unordered natural sum of p plus the unordered natural sum of q. Separate absolute convergence is a conclusion. The definition does not use a logarithm, a cancellation premise or an assumed convergence proof.

**Definition 1.4 (The ordinary complex bilateral family).**

$$\forall x \in \mathbb{C},\; \forall a \in \operatorname{Nonzero}\left(\mathbb{C}\right),\; \forall n \in \operatorname{Nonzero}\left(\mathbb{Z}\right),\; \operatorname{raw}\left(x, a, n\right) = \frac{\left(x - a^{n}\right)^{n}}{n}$$

*Formalization.* `D5/S3/Analytic/PowerSeries/BalaBilateralLog.raw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2025). *The bilateral logarithm conjecture in OEIS A292179 and A292178*. URL: <https://oeis.org/A292179>.

*Commentary.*

Nonzero(C) means the subtype of complex parameters a!=0, and Nonzero(Z) means integers n!=0. All powers displayed here are ordinary integer powers. There is no raw family at parameter zero and no raw term at integer index zero.

**Definition 1.5 (The original real source family).**

$$\forall x \in \mathbb{R},\; \forall a \in \operatorname{Nonzero}\left(\mathbb{R}\right),\; \forall n \in \operatorname{Nonzero}\left(\mathbb{Z}\right),\; \operatorname{realRaw}\left(x, a, n\right) = \frac{\left(x - a^{n}\right)^{n}}{n}$$

*Formalization.* `D5/S3/Analytic/PowerSeries/BalaBilateralLog.realRaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2025). *The bilateral logarithm conjecture in OEIS A292179 and A292178*. URL: <https://oeis.org/A292179>.

*Commentary.*

The real source family uses real arithmetic and ordinary integer powers, with nonzero real a and nonzero integer n. Complexification preserves each term.

**Theorem 1.6 (The complete full-domain identity and extension).**

Lean statement: `D5/S3/Analytic/PowerSeries/BalaBilateralLog.full_event`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PowerSeries/BalaBilateralLog.full_event` (`✓ std3`). ∎

*Resolves.* `Problems/bala-a292179-a292178-bilateral-logarithm` (proved) by `D5/S3/Analytic/PowerSeries/BalaBilateralLog.full_event`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala-a292179-a292178-bilateral-logarithm","declaration_gid":"D5/S3/Analytic/PowerSeries/BalaBilateralLog.full_event","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2025). *The bilateral logarithm conjecture in OEIS A292179 and A292178*. URL: <https://oeis.org/A292179>.

*Commentary.*

For every complex x,a with norm(x)<1 and norm(a)<1 separately, the norm series of positive(x,a,k) and negative(x,a,k) are summable, and F(x,a)=-Complex.log(1-x). Complex.log is Mathlib's principal complex logarithm. For every natural k, k+1 and 1-x*a^(k+1) are nonzero. Moreover Re(1-x)>0. No combined-norm, sign, diagonal or smaller-disk condition is imposed.

For every such x and every nonzero a in its unit disk, and every integer n!=0, a^n and the complex integer divisor n are nonzero; if n<0, x-a^n is nonzero as well. For every k>=0, raw(x,a,k+1)=positive(x,a,k) and raw(x,a,-(k+1))=negative(x,a,k). The norm family over all nonzero integers is summable. HasSum of that unordered family has value F, its tsum equals F, and the sum of its separately indexed positive and negative tails equals F. The finite symmetric sums over k=0,...,N-1 of raw(k+1)+raw(-(k+1)) tend to F as N tends to infinity. These are the source truncations over -N,...,-1,1,...,N.

For every real x and nonzero real a with abs(x)<1 and abs(a)<1, realRaw is absolutely summable and HasSum realRaw (-Real.log(1-x)). In particular negative x and negative a are included. Since 1-x>0, Complex.ofReal_log identifies the principal complex value with the embedded real logarithm. This is an identity of the original real series, not only an identity of a complex formula.

For each fixed complex x in its unit disk, positive(x,0,k)=x^(k+1)/(k+1) and negative(x,0,k)=0 for every k. The independently defined F(x,a) is continuous at a=0. If any H:C->C is continuous at zero within the open a-disk and equals the punctured raw unordered sum at every nonzero a in that disk, then H=F throughout that disk. Values of H outside the disk are unconstrained. The proof establishes continuity and uniqueness separately; it assigns no value to the raw expression at a=0.

Put c(n,m)=0 for m=0 and c(n,m)=(-a^n)^m*x^(n-m)*choose(n,m)/n otherwise. Its finite row of norms is bounded by (norm(x)+norm(a)^n)^n. Choose rho=(1+norm(x))/2<1; eventually norm(a)^n<rho-norm(x), so this row majorant is dominated by rho^n. This proves joint absolute summability before any change of order. The finite binomial theorem gives the row sum ((x-a^n)^n-x^n)/n. The negative-binomial HasSum supplier at x*a^(k+1), whose norm is less than one, gives the column sum -q_(k+1). Absolute Fubini cancellation leaves sum x^n/n, identified by Complex.hasSum_taylorSeries_neg_log. The raw bridges use nonzero ordinary powers. Uniqueness uses the nontrivial punctured neighborhood filter at zero.

The fixed source comments in A292179 and A292178 pose one question. The paired entries do not represent two independent settlements. The cited source note gives the exact quotations, parameter interpretation and bounded literature limitations; no global novelty or priority claim is made.

## References

- Truth anchor: `D5/S3/Analytic/PowerSeries/BalaBilateralLog.full_event`
- Truth anchor: `D5/S3/Analytic/PowerSeries/BalaBilateralLog.negative`
- Truth anchor: `D5/S3/Analytic/PowerSeries/BalaBilateralLog.positive`
- Truth anchor: `D5/S3/Analytic/PowerSeries/BalaBilateralLog.raw`
- Truth anchor: `D5/S3/Analytic/PowerSeries/BalaBilateralLog.realRaw`
- Truth anchor: `D5/S3/Analytic/PowerSeries/BalaBilateralLog.regularSum`
