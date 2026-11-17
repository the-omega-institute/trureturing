# The complete actual zero series under RH

## Abstract

Actual zero mass and arbitrarily late positive phase recurrence

**Definition 1.1 (The normalized complete Mertens primitive).**

$$\forall y \in \mathbb{R},\; \operatorname{G}\left(y\right) = \operatorname{exp}\left(\frac{-y}{2}\right) \cdot \operatorname{U}\left(\operatorname{exp}\left(y\right)\right)$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real function U is CompleteMertensPeak.U, with the complete inclusive Mangoldt sum. The normalization is defined on every real y.

Write M=ActualReciprocalSquareBounds.firstLiMass, and use the canonical actualZero, actualCoeff and actualH of ActualZeroLaplace. Every natural index is an actual analytic zero occurrence through actualOccurrenceEquiv, including its multiplicity. Both conjugate signs are included.

**Theorem 1.2 (Eventual absolute control and arbitrarily late values near the positive mass).**

$$\operatorname{RiemannHypothesis} \Rightarrow \left(\left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists T \in \mathbb{R},\; \forall y \in \mathbb{R},\; T \le y \Rightarrow \left|\operatorname{G}\left(y\right)\right| < firstLiMass + epsilon\right)\right) \land \left(\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\forall Y \in \mathbb{R},\; \exists n \in \mathbb{N},\; Y \le n \land \left|\operatorname{G}\left(n\right) - firstLiMass\right| < epsilon\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.actual_G_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For G(y)=exp(-y/2)*U(exp y), the conclusion under RiemannHypothesis contains both: for each epsilon>0, eventually on all real y, abs(G(y))<M+epsilon; and for each epsilon>0 and real Y, a natural n exists with n>=Y and abs(G(n)-M)<epsilon.

RH puts Re(actualZero(k))=1/2. Multiplication gives rho*(1-rho)=1/4+Im(rho)^2, so actualCoeff(k) is a positive real complex number and its norm is its real part. Apply Complex.hasSum_re to the canonical actualCoeff_hasSum: the complete norm mass is exactly M. Since norm(exp(y*rho))=exp(y/2), the triangle inequality for the absolutely summable full series gives norm(exp(-y/2)*actualH(y))<=M for every real y.

On the compact infinite product group Z=(Nat -> Circle), put g(k)=Circle.exp(Im(rho(k))) and F(z)=tsum_k actualCoeff(k)*(z(k):Complex). Circle.exp uses exp(t*I), with no 2*pi. Each summand is continuous and has norm at most norm(actualCoeff(k)), independently of z. FunctionSeries.continuous_tsum therefore gives continuity on the entire product. The existing coefficient HasSum gives F(1)=M. Circle.coe_exp, pointwise powers and Complex.exp_nat_mul identify F(g^n)=exp(-n/2)*actualH(n) for every natural n. The identity is between complete summable series, by multiplication by one common scalar.

Apply mapClusterPt_one_atTop_pow on this compact product, followed by MapClusterPt.continuousAt_comp and MapClusterPt.frequently. Every neighborhood of M contains F(g^n) for arbitrarily large natural n. This requires neither linear independence nor a rate or shrinking target.

WholeFormula gives exactly G(y)=Re(exp(-y/2)*actualH(y))+residual(y) for y>0, where residual(y)=exp(-y/2)*(log(2*pi)-trivialT(y)). The complete trivial-zero bounds 0<=trivialT(y)<=1-log(2) for y>=0 imply residual(y)->0. Complex.abs_re_le_norm controls the real phase error directly. Eventual control follows from the norm bound. For recurrence, combine a phase error below epsilon/2 with the residual below epsilon/2 and the required lower bound on n. The real-part estimate transfers the complex phase recurrence to G.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.G`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.actual_G_control`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula](WholeFormula.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RhLocatesZeroData](../../ZetaBridge/RhLocatesZeroData.md)
