# ProfiniteQuotientBound

## Abstract

Uniform finite quotient bounds control closed normal quotients.

**Definition 1.1 (Uniform finite exponent order bound).**

$$\operatorname{FiniteExponentBound}(d, m, B) \iff \forall (Q: Type), {\operatorname{Group}(Q) \land \operatorname{Finite}(Q)} \Rightarrow {{\operatorname{GeneratedByAtMost}(Q, d) \land \forall (q: Q), q^{m} = 1} \Rightarrow {\operatorname{Card}(Q) \leq B}}$$

*Formalization.* `D5/S3/Factorization/Galois/ProfiniteQuotientBound.FiniteExponentBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For fixed d, m and B, every finite group with at most d algebraic generators and every element having mth power one has order at most B. This proposition is an explicit unproved finite-group input, of the restricted Burnside form.

**Theorem 1.2 (A closed normal quotient is finite).**

$${\operatorname{CompactTotallyDisconnectedTopologicalGroup}(G)} \Rightarrow {\forall (P: \operatorname{ClosedNormalSubgroup}(G)), \forall (B: \mathbb{N}), {\forall (N: \operatorname{OpenNormalSubgroup}(G)), {P \leq N} \Rightarrow {\operatorname{Index}(N) \leq B}} \Rightarrow {\operatorname{Finite}(\operatorname{Quotient}(G, P))}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ProfiniteQuotientBound.closed_normal_finite_quotient_of_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be any closed normal subgroup of a compact totally disconnected topological group. If the indices of all open normal subgroups containing P are at most B, then G modulo P is finite. A maximal index forces a least open normal subgroup; closed-set separation identifies it with P. This includes nontrivial P and assumes no dense generators.

**Theorem 1.3 (Exponent bounds transfer through a closed power subgroup).**

$${\operatorname{CompactTotallyDisconnectedTopologicalGroup}(G)} \Rightarrow {{\operatorname{TopologicalClosure}(\operatorname{SubgroupClosure}(S)) = \operatorname{TopSubgroup}(G)} \Rightarrow {{\operatorname{IsClosed}(\operatorname{powerSubgroup}(G, m)) \land \operatorname{FiniteExponentBound}(\operatorname{Card}(S), m, B)} \Rightarrow {\operatorname{Finite}(\operatorname{Quotient}(G, \operatorname{powerSubgroup}(G, m)))}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ProfiniteQuotientBound.finite_power_quotient_of_exponent_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For dense finite generators S and a closed power subgroup, the uniform finite exponent order bound applies to every continuous finite quotient killing that subgroup. The general closed normal quotient theorem then makes the power quotient finite.

**Theorem 1.4 (Openness from the two finite-group inputs).**

$${\operatorname{CompactTotallyDisconnectedTopologicalGroup}(G)} \Rightarrow {{\operatorname{TopologicalClosure}(\operatorname{SubgroupClosure}(S)) = \operatorname{TopSubgroup}(G)} \Rightarrow {{\operatorname{FinitePowerWidth}(\operatorname{Card}(S), m, w) \land \operatorname{FiniteExponentBound}(\operatorname{Card}(S), m, B)} \Rightarrow {\operatorname{IsOpen}(\operatorname{powerSubgroup}(G, m))}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ProfiniteQuotientBound.isOpen_powerSubgroup_of_finite_inputs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a compact totally disconnected topological group with dense generators S, a finite power-width bound and a finite exponent order bound at the same m imply openness of the power subgroup. Both finite-group inputs remain assumptions.

**Theorem 1.5 (Arbitrary finite-index subgroups).**

$${\operatorname{CompactTotallyDisconnectedTopologicalGroup}(G)} \Rightarrow {{\operatorname{TopologicalClosure}(\operatorname{SubgroupClosure}(S)) = \operatorname{TopSubgroup}(G)} \Rightarrow {\forall (H: \operatorname{Subgroup}(G)), {\operatorname{FiniteIndex}(H)} \Rightarrow {{\operatorname{FinitePowerWidth}(\operatorname{Card}(S), \operatorname{Index}(\operatorname{NormalCore}(H)), w) \land \operatorname{FiniteExponentBound}(\operatorname{Card}(S), \operatorname{Index}(\operatorname{NormalCore}(H)), B)} \Rightarrow {\operatorname{IsOpen}(H)}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ProfiniteQuotientBound.finiteIndex_isOpen_of_finite_inputs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite-index subgroup H, the two finite-group inputs at its positive normal-core index make the contained power subgroup open. Therefore H is open. H is not assumed normal.

## References

- Truth anchor: `D5/S3/Factorization/Galois/ProfiniteQuotientBound.FiniteExponentBound`
- Truth anchor: `D5/S3/Factorization/Galois/ProfiniteQuotientBound.closed_normal_finite_quotient_of_bound`
- Truth anchor: `D5/S3/Factorization/Galois/ProfiniteQuotientBound.finiteIndex_isOpen_of_finite_inputs`
- Truth anchor: `D5/S3/Factorization/Galois/ProfiniteQuotientBound.finite_power_quotient_of_exponent_bound`
- Truth anchor: `D5/S3/Factorization/Galois/ProfiniteQuotientBound.isOpen_powerSubgroup_of_finite_inputs`
- Dependency: [D5/S3/Factorization/Galois/ProfinitePowerTransfer](ProfinitePowerTransfer.md)
