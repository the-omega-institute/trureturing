# Rational Interval Every-Radius Witness

## Abstract

The fixed rational interval phase-memory map is not self-tuning on any positive closed restriction, with the original geometric weighted-sum antecedent.

Use I=[0,1], f(u)=2u/(1+u), delta=1/256 and the full closed domains P_r of integer sequences with e(x,k)=d(x(k+1),f(x(k)))<=r. The same maps R and T(x)=action(1+memory(x),R(x)) are those of RationalIntervalRetraction and RationalIntervalPhaseMemory; evaluation on P_r means literal inclusion into P_delta. Write O(p)(j)=f^j(p), shift(i,x)(j)=x(i+j), and D(x,y)=sum over all j in Z of 2^(-|j|)d(x(j),y(j)). Artigue's Definition 5.1 uses exactly this D with the allowed parameter 1/2. The construction and calculations below are separate from the cited paper.

For natural m and n>=1 let p=2^(-m), q=1/2, and h=f(p)=2/(2^m+1). Define x_(m,n)(k)=p at k=-1, f^(k-2n)(q) for k>=n, and zero otherwise. These disjoint cases give zero for k<-1 and for 0<=k<n. Put B(m)=1/[2(2^m+2)]. For the formulas below M(x)={k:1/3<x(k)<2/3}; T on a displayed witness always means the same fixed T after inclusion, never a newly chosen map.

**Theorem 1.1 (The three exact link errors).**

$$\begin{aligned}\forall m\in \mathbb{N}, \forall n\in \mathbb{N}, 1\le n\Rightarrow e(x_{m,n},-2)=\frac{1}{2}^{m}\land e(x_{m,n},-1)=\frac{2}{2^{m}+1}\land e(x_{m,n},n-1)=\frac{1}{2^{n}+1}\land \\\forall k\in \mathbb{Z}, k\neq -2\land k\neq -1\land k\neq n-1\Rightarrow e(x_{m,n},k)=0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.witness_link_errors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The links at -2 and -1 are the isolated early pulse; the link at n-1 enters the genuine tail from zero. All other links are zero or genuine orbit steps. The assumption n>=1 makes these three indices distinct, including n=1. The exact support is {-2,-1,n-1}.

**Theorem 1.2 (Singleton marker and both boundary neighbors).**

$$\begin{aligned}\forall m\in \mathbb{N}, \forall n\in \mathbb{N}, 3\le m\land 1\le n\Rightarrow M(x_{m,n})=\{2n\}\land x_{m,n}(2n-1)=\frac{1}{3}\land x_{m,n}(2n+1)=\frac{2}{3}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.witness_marker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The early point is at most 1/8. For the tail, f^k(q)=2^k/(1+2^k) is strictly between 1/3 and 2/3 exactly when the integer k is zero. The coordinates immediately adjacent to 2n are exactly 1/3 and 2/3, and are unmarked under the strict band definition.

**Theorem 1.3 (Exact fixed positive defect).**

$$\begin{aligned}\forall r\in \mathbb{R}, r\le \frac{1}{256}\Rightarrow \forall m\in \mathbb{N}, \forall n\in \mathbb{N}, 3\le m\land 1\le n\land x_{m,n}\in P_{r}\Rightarrow d(f^{2n}(T(x_{m,n})),T(shift(2n,x_{m,n})))=\frac{1}{2(2^{m}+2)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.witness_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

At the sole marker q, weight(q)=1/36 and weightedOdds(q)=1/36. The actual finite sums give W(x)=1/36 and A(x)=2^(-2n)/36, hence R(x)=f^(-2n)(q). This is a direct evaluation of the defining quotient, rather than an inference from equivariance alone. The origin memory is h, the shifted memory at 2n is zero, and x(2n)=q. Thus T(shift(2n,x))=q and f^(2n)T(x)=action(1+h,q). The exact distance is h/(4+2h)=B(m)>0, independent of n.

**Theorem 1.4 (The literal weighted-sum bound).**

$$\begin{aligned}\forall m\in \mathbb{N}, \forall n\in \mathbb{N}, 1\le n\Rightarrow D(shift(2n,x_{m,n}),O(x_{m,n}(2n)))\le \frac{1}{2}^{n}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.witness_weightedDistance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

For every integer j>=-n the index 2n+j belongs to the true tail, so the shifted sequence agrees with O(q) on that entire half-line. Apply weightedDistance_le_negative_tail to the genuinely infinite sum; all earlier discrepancies together contribute at most 2^(-n). No replacement metric is involved.

**Theorem 1.5 (One early pulse for each positive restriction).**

$$\begin{aligned}\forall r\in \mathbb{R}, 0<r\le \frac{1}{256}\Rightarrow \exists m\in \mathbb{N}, 3\le m\land 2^{1-m}<r\land \\\forall a\in \mathbb{R}, 0<a\Rightarrow \exists n\in \mathbb{N}, 1\le n\land \frac{1}{2}^{n}<min(r,a)\land x_{m,n}\in P_{r}\land Finite(support(linkError(x_{m,n})))\land D(shift(2n,x_{m,n}),O(x_{m,n}(2n)))<a\land d(f^{2n}(T(x_{m,n})),T(shift(2n,x_{m,n})))=\frac{1}{2(2^{m}+2)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.T_every_rho_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Choose m>=3 once with 2^(1-m)<r, so p<r and h<=2p<r. For any a>0 choose only n>=1 with 2^(-n)<min(r,a). The three-error formula puts the whole sequence in the fixed closed P_r, its error support is finite, the original weighted antecedent is strictly less than a, and the defect remains the same positive B(m).

**Theorem 1.6 (Failure of the literal Definition 5.1 on every positive restriction).**

$$\begin{aligned}\forall r\in \mathbb{R}, 0<r\le \frac{1}{256}\Rightarrow \neg SelfTuningOn(r)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.T_not_self_tuning_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Here SelfTuningOn(r) means: for every epsilon>0 there is a>0 such that, for every x in the full P_r and every i in Z, D(shift(i,x),O(x(i)))<a implies d(f^i T(x),T(shift(i,x)))<=epsilon. Fix epsilon=B(m)/2 before a is chosen. The preceding witnesses have strict antecedent and defect B(m)>epsilon for every a>0. Together with T_shadowing_map and T_L_shadowing_map this separates the original L-shadowing-map property from self-tuning for this prescribed T. Those positive results retain the full closed domain and arbitrary infinitely supported two-sided limit errors. On any positive smaller restriction their scales can be reduced by taking the minimum with its radius. The result concerns the specified map; it makes no assertion that the same dynamics lacks other self-tuning selectors.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.T_every_rho_witness`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.T_not_self_tuning_on`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.witness_defect`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.witness_link_errors`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.witness_marker`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalWitness.witness_weightedDistance`
- Dependency: [D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory](RationalIntervalPhaseMemory.md)
- Dependency: [D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance](RationalIntervalWeightedDistance.md)
