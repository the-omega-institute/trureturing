# Fixed Fiber Pair Modulus

## Abstract

One selected continuation has exact scalar and matrix moduli on the entire positive rank-one source fiber of its fixed executed history.

**Theorem 1.1 (Upper shear powers).**

Lean statement: `D5/S3/Observer/TraceFibers/FixedFiberPairModulus.upper_shear_power`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/TraceFibers/FixedFiberPairModulus.upper_shear_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kth power of JM has rows (1,k) and (0,1), including the identity at k=0.

**Theorem 1.2 (Lower shear powers).**

Lean statement: `D5/S3/Observer/TraceFibers/FixedFiberPairModulus.lower_shear_power`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/TraceFibers/FixedFiberPairModulus.lower_shear_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kth power of MJ has rows (1,0) and (k,1), the transpose of the upper shear power.

**Theorem 1.3 (Exact moduli from a common source pair).**

$$\begin{aligned}x > 0, \zeta > 0, \tau \ge 0, e > 0\\\alpha = \frac{e}{\zeta}, \mu = \operatorname{abs}(D)-\alpha\cdot x \ge 0\\w = \operatorname{min}(x, \frac{\sqrt{\mu^{2}+4\cdot\alpha\cdot\tau}-\mu}{2\cdot\alpha}), b = \operatorname{min}(w, \frac{x}{2})\\\operatorname{Omega}_{B}(\tau) = w, \mathcal{M}_{B}(\tau) = \operatorname{max}(w, \frac{b\cdot{x-b}}{\zeta})\\\tau > 0 \Rightarrow \text{positive unattained}(\operatorname{Omega}_{B}(\tau), \mathcal{M}_{B}(\tau))\\\tau = 0 \Rightarrow \operatorname{Omega}_{B}(\tau) = \mathcal{M}_{B}(\tau) = 0, \text{attained at equal pair}(\frac{x}{2})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/TraceFibers/FixedFiberPairModulus.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The permitted atomic matrices are M with rows (0,1),(1,1), and J with rows (0,1),(1,0). A word lists operations chronologically, so its later operations multiply on the left. Fix the entire executed prefix, whose endpoint is U^k or V^k with U=JM, V=MJ and k at least one. The initial identity read counts; there are three reads and the total action count is the prefix length plus the selected continuation length.

For positive x and zeta, positive rank-one sources with initial read x and second read x+k*zeta are exactly R(s), 0<s<x. The upper fiber has rows (x-s,s*(x-s)/zeta),(zeta,s); the lower fiber has rows (x-s,zeta),(s*(x-s)/zeta,s). Every positive rank-one source factors as a positive column times a positive fixed measurement row. Every cumulative read is the fixed row applied to the transformed column.

Select one legal continuation before its third read, and set B to its matrix times the prefix matrix. On the upper fiber e=B21; on the lower fiber e=B12. Put D=B22-B11, alpha=e/zeta and mu=abs(D)-alpha*x. Assume e>0 and mu>=0, retaining both signs of D and the equality case mu=0.

Both suprema use exactly the same pairs u,v in (0,x) whose raw third trace readings differ by at most tau. Equal pairs are allowed. Scalar distance is abs(u-v), and matrix distance is the maximum absolute entry among all four entries of R(u)-R(v). Neither supremum is defined by its closed formula.

Writing l=abs(u-v) and z=x-u-v gives readout distance l*abs(D+alpha*z) and matrix distance max(l,l*abs(z)/zeta). An unequal interior pair has abs(z)<x-l, so its readout distance strictly exceeds mu*l+alpha*l^2. This bounds spacing by the clipped root and the matrix objective by the geometric envelope.

For each positive spacing below the clipped root and each threshold below l*(x-l)/zeta, a single interior pair simultaneously satisfies the readout constraint and exceeds the objective threshold. A positive endpoint displacement is chosen to preserve the domain, readout slack and matrix margin. Reflecting the pair handles the other sign of D. These common pairs supply both supremum lower bounds, including the capped root and its boundary.

For positive tolerance both suprema are positive and every feasible interior pair lies strictly below them. At zero tolerance both are zero and the equal pair s=x/2 attains them. All sources and reads belong to the same executed history and chosen continuation; the model introduces no reset, copy, inverse operation or unexecuted branch.

## References

- Truth anchor: `D5/S3/Observer/TraceFibers/FixedFiberPairModulus.lower_shear_power`
- Truth anchor: `D5/S3/Observer/TraceFibers/FixedFiberPairModulus.result`
- Truth anchor: `D5/S3/Observer/TraceFibers/FixedFiberPairModulus.upper_shear_power`
- Dependency: [D5/S3/Observer/GoldenCoding/GoldenModularStandardPair](../GoldenCoding/GoldenModularStandardPair.md)
- Dependency: [D5/S3/Observer/HyperbolicTransport/GoldenDualTimeRenormalization](../HyperbolicTransport/GoldenDualTimeRenormalization.md)
