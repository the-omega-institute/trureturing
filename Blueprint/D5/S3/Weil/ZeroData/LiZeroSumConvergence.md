# Li Zero-Sum Convergence

## Abstract

The real Li series over actual zeta zeros is absolutely summable, and three conjugate-paired cutoff sums converge to its real value.

Z is any exhaustive, injective enumeration of the actual nontrivial zeros of the Riemann zeta function, with exact positive analytic multiplicities. In particular, the existing zetaZeroData in UnconditionalCanonicalZeroData is a canonical instance. The natural index n includes zero. Set rho_k=Z.zero(k), m_k=Z.multiplicity(k), and gamma_k=-i*(rho_k-1/2). The strict strip 0<Re(rho_k)<1 is part of the actual-zero data.

**Theorem 1.1 (Absolute summability of the real parts).**

$$\forall Z\in\operatorname{ZeroData}, \forall n\in\mathbb{N}, \operatorname{Summable}(k\mapsto m_{k}(1-\Re((1-\frac{1}{rho_{k}})^{n})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/LiZeroSumConvergence.li_zero_real_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The summand is m_k*(1-Re((1-1/rho_k)^n)). For |gamma_k|>=2 its absolute value is at most 4*2^n*m_k/(1+|gamma_k|^2). First-order real-part cancellation supplies the inverse-square decay: for u=1/rho_k, |Re(u)|<=|u|^2, and a power induction bounds |1-Re((1-u)^n)| by (2^n-1)*|u|^2. The existing reciprocal-square zeta-weight theorem makes this majorant summable. All remaining low-zero terms form a finite set and are retained. The factor 4*2^n is a convergence majorant, not a value of the first Li coefficient.

**Theorem 1.2 (Spectral, height, and radial cutoffs have the same limit).**

$$\forall Z\in\operatorname{ZeroData}, \forall n\in\mathbb{N}, \operatorname{Tendsto}((T\mapsto\sum_{k\in\operatorname{Sgamma}(T)} m_{k}(1-(1-\frac{1}{rho_{k}})^{n})), atTop, \operatorname{nhds}(\sum_{k=0}^{\infty} m_{k}(1-\Re((1-\frac{1}{rho_{k}})^{n}))))\land \operatorname{Tendsto}((T\mapsto\sum_{k\in\operatorname{Sheight}(T)} m_{k}(1-(1-\frac{1}{rho_{k}})^{n})), atTop, \operatorname{nhds}(\sum_{k=0}^{\infty} m_{k}(1-\Re((1-\frac{1}{rho_{k}})^{n}))))\land \operatorname{Tendsto}((T\mapsto\sum_{k\in\operatorname{Sradial}(T)} m_{k}(1-(1-\frac{1}{rho_{k}})^{n})), atTop, \operatorname{nhds}(\sum_{k=0}^{\infty} m_{k}(1-\Re((1-\frac{1}{rho_{k}})^{n}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/LiZeroSumConvergence.li_zero_cutoff_limits` (`✓ std3`). ∎

*Citation.* Jeffrey C. Lagarias (2004). *Li Coefficients for Automorphic L-Functions*. URL: <https://arxiv.org/abs/math/0404394v4>.

*Commentary.*

Every finite summand is m_k*(1-(1-1/rho_k)^n). The three index sets contain exactly the zeros satisfying |gamma_k|<=T, |Im(rho_k)|<=T, and |rho_k|<=T, respectively; these are Sgamma(T), Sheight(T), and Sradial(T) in the formula. T is real, atTop means T tends to positive infinity, and nhds is the complex neighborhood filter of the displayed real sum cast into C. The latter two sets are filters of the spectral ball at T+1; their membership equalities hold for all real T, including nonpositive cutoffs. Each set is invariant under complex conjugation and eventually contains every finite set of indices. Finite conjugate pairing makes each complex sum the cast of its real-part sum. Absolute real summability then gives the three limits. Lagarias equation (1.1) uses the radial convention; Suzuki equation (1.1) uses the height convention, as detailed in the source note.

**Remark 1.3 (Presentation independence and the derivative identity).**

Lean statement: `D5/S3/Weil/ZeroData/LiZeroSumConvergence.li_zero_cutoff_limits`

*Formalization.* `D5/S3/Weil/ZeroData/LiZeroSumConvergence.li_zero_cutoff_limits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing zeroEquiv transports the absolutely summable real series between any two actual-zero presentations; the exact multiplicities are identified by multiplicity_eq_zeroMult. No second Li sequence is defined. Identifying this common limit with the canonical derivative coefficient remains a separate open identity. These theorems assume no Riemann hypothesis, representation formula, or convergence premise, and assert no absolute summability of the unpaired complex terms.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/LiZeroSumConvergence.li_zero_cutoff_limits`
- Truth anchor: `D5/S3/Weil/ZeroData/LiZeroSumConvergence.li_zero_cutoff_limits`
- Truth anchor: `D5/S3/Weil/ZeroData/LiZeroSumConvergence.li_zero_real_summable`
