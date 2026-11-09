# A Proper Integer Orbit Clock

## Abstract

Literal pointwise north-south dynamics supplies a continuous strict height through locally finite integer orbit sums.

**Theorem 1.1 (The height is constructed from pointwise dynamics).**

$$\forall M: CompactMetricSpace, \forall f: \operatorname{Homeomorphism}(M), \forall N: M, \forall S: M, \operatorname{Pointwise}(f, N, S) \Rightarrow \operatorname{Nonempty}(\operatorname{StrictHeight}(f, N, S))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/NorthSouthOrbitClock.exists_strictHeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The assumptions are precisely Pointwise f N S on an arbitrary compact metric space. The resulting continuous real height takes values in [-1,1], takes -1 exactly at N and 1 exactly at S, and strictly increases under f at every other point. No height, clock, flow, rate, stability or uniformity is assumed.

The raw distance difference d(p,N)-d(p,S) has the same zero cut as the normalized distance function because d(p,N)+d(p,S)>0. The compact set u(p)≤0≤u(f(p)) meets each punctured orbit. A continuous nonnegative bump is positive on that cut and vanishes near both poles. Compact uniform attraction bounds its nonzero integer translates on every compact subset of the punctured space, hence locally. Thus B(p)=sum b(f^i(p)) and A(p)=sum i b(f^i(p)) are actual finite sums with B>0.

Finite reindexing gives B(fp)=B(p), A(fp)=A(p)-B(p), and t(fp)=t(p)+1 for t=-A/B. Stability at the poles forces all positive-weight indices to escape in the appropriate direction, so t tends to positive infinity at S and negative infinity at N. The compression t/(1+abs(t)) extends continuously with the prescribed endpoint values. If the punctured space is empty, its clock obligations are vacuous and the same extension covers the two-point space.

This follows the supplied proof SHA-256 9d2c8af332171841b0de2122a8a6d18d3f094b8ee563ff2b50646332144306bc and formal route SHA-256 1a51a2083580f57293ae2e0f032afb5257d891328f247d26b97b81b483360a97. The reusable inference added here is the derived proper clock and its endpoint extension; the result alone is not the full selector theorem.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/NorthSouthOrbitClock.exists_strictHeight`
- Dependency: [D5/S1/Dynamics/Shadowing/PointwiseNorthSouth](PointwiseNorthSouth.md)
