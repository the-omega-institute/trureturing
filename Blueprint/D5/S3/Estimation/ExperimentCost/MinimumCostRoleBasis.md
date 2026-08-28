# Minimum-Cost Role Bases

## Abstract

Cost-ordered independence scanning finds minimum-cost finite linear-role bases.

**Definition 1.1 (Role basis).**

Lean statement: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.IsRoleBasis`

*Formalization.* `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.IsRoleBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite role set is independent and spans all available role vectors.

**Definition 1.2 (Linear role matroid).**

Lean statement: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.linearRoleMatroid`

*Formalization.* `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.linearRoleMatroid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The independent sets are exactly the labels of linearly independent role vectors.

**Definition 1.3 (Greedy role scan from a chosen set).**

Lean statement: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.greedyRoleScanFrom`

*Formalization.* `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.greedyRoleScanFrom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each scanned label is inserted exactly when independence is preserved.

**Definition 1.4 (Greedy role scan).**

Lean statement: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.greedyRoleScan`

*Formalization.* `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.greedyRoleScan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public algorithm discards duplicate scan labels and starts from the empty chosen set.

**Definition 1.5 (Set cover).**

Lean statement: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.IsSetCover`

*Formalization.* `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.IsSetCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A chosen finite family covers when its union contains the ground set.

**Definition 1.6 (Set-cover counterexample family).**

Lean statement: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.setCoverExample`

*Formalization.* `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.setCoverExample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three explicit subsets of a six-element ground set witness greedy suboptimality.

**Theorem 1.7 (Matroid independence is linear independence).**

$$\operatorname{Indep}\left(\operatorname{linearRoleMatroid}\left(v\right), S\right) \iff \operatorname{LinearIndepOn}\left(v, S\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.linearRoleMatroid_indep_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed matroid exposes precisely the original linear independence predicate.

**Theorem 1.8 (Matroid bases are role bases).**

$$\operatorname{IsBase}\left(\operatorname{linearRoleMatroid}\left(v\right), S\right) \iff \operatorname{IsRoleBasis}\left(v, S\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.linearRoleMatroid_isBase_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Maximal matroid independence is equivalent to independence together with spanning every available role vector.

**Theorem 1.9 (Greedy scanning gives a minimum-cost role basis).**

$$\operatorname{Exhaustive}\left(L\right) \land \operatorname{Nondecreasing}\left(c, L\right) \Rightarrow\\\operatorname{IsRoleBasis}\left(v, \operatorname{greedyRoleScan}\left(v, L\right)\right) \land \forall B, \operatorname{IsRoleBasis}\left(v, B\right) \Rightarrow \operatorname{totalCost}\left(c, \operatorname{greedyRoleScan}\left(v, L\right)\right) \leq \operatorname{totalCost}\left(c, B\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.greedy_role_scan_is_minimum_cost_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an exhaustive scan in nondecreasing cost order, the output is a role basis whose real total cost is no larger than any other role basis. No finiteness or duplicate-free hypothesis is exposed.

**Theorem 1.10 (Negative costs preserve greedy optimality).**

$$\exists e, \operatorname{cost}\left(c, e\right) < 0 \land \operatorname{MinimumCostBasis}\left(c, \operatorname{greedyRoleScan}\left(v, L\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.negative_costs_preserve_greedy_optimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A one-role family with cost minus one instantiates the general theorem. Thus nonnegativity is not a necessary hypothesis.

**Theorem 1.11 (Equal-cost role bases have equal totals).**

$$\operatorname{IsRoleBasis}\left(v, B_{1}\right) \land \operatorname{IsRoleBasis}\left(v, B_{2}\right) \Rightarrow\\\operatorname{constantTotal}\left(a, B_{1}\right) = \operatorname{constantTotal}\left(a, B_{2}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.equal_cost_role_bases_have_equal_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All bases of the linear role matroid have equal cardinality, so a constant role cost gives every basis the same total.

**Theorem 1.12 (Empty role scan).**

$$\operatorname{greedyRoleScan}\left(v, \operatorname{emptyScan}\left(\right)\right) = \emptyset \land \operatorname{IsRoleBasis}\left(v, \emptyset\right) \land \operatorname{MinimumCostBasis}\left(c, \emptyset\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.empty_role_scan_degenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the empty role type, the greedy result is empty and is the unique minimum-cost role basis.

**Theorem 1.13 (A singleton zero role is skipped).**

$$\operatorname{greedyRoleScan}\left(\operatorname{zeroRole}\left(\right), \operatorname{singletonScan}\left(0\right)\right) = \emptyset \land \operatorname{IsRoleBasis}\left(\operatorname{zeroRole}\left(\right), \emptyset\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.singleton_zero_role_is_skipped` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero vector cannot extend the empty independent set; omitting its label still spans the available zero role.

**Theorem 1.14 (A singleton nonzero role is selected).**

$$\operatorname{greedyRoleScan}\left(\operatorname{unitRole}\left(\right), \operatorname{singletonScan}\left(0\right)\right) = \operatorname{singleton}\left(0\right) \land \operatorname{IsRoleBasis}\left(\operatorname{unitRole}\left(\right), \operatorname{singleton}\left(0\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.singleton_nonzero_role_is_selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A lone nonzero rational vector is accepted and forms the singleton role basis.

**Theorem 1.15 (Exhaustive scanning is necessary).**

$$\operatorname{greedyRoleScan}\left(\operatorname{unitRole}\left(\right), \operatorname{emptyScan}\left(\right)\right) = \emptyset \land \neg\operatorname{IsRoleBasis}\left(\operatorname{unitRole}\left(\right), \emptyset\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.exhaustive_scan_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An empty scan on a single nonzero role returns empty, which cannot span that role. Thus coverage of every label is a genuine premise.

**Theorem 1.16 (Cost order is necessary).**

$$\neg\operatorname{Nondecreasing}\left(\operatorname{costPair}\left(1, 0\right), \operatorname{scan}\left(0, 1\right)\right) \land \operatorname{greedyRoleScan}\left(\operatorname{equalVectorPair}\left(\right), \operatorname{scan}\left(0, 1\right)\right) = \operatorname{singleton}\left(0\right) \land\\\operatorname{IsRoleBasis}\left(\operatorname{equalVectorPair}\left(\right), \operatorname{singleton}\left(1\right)\right) \land \operatorname{totalCost}\left(\operatorname{costPair}\left(1, 0\right), \operatorname{singleton}\left(1\right)\right) < \operatorname{totalCost}\left(\operatorname{costPair}\left(1, 0\right), \operatorname{singleton}\left(0\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.sorted_scan_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two equal nonzero vectors have costs one and zero. Scanning the dearer label first selects cost one, although the other singleton basis has cost zero.

**Theorem 1.17 (A mixed zero role is skipped).**

$$\operatorname{greedyRoleScan}\left(\operatorname{zeroUnitPair}\left(\right), \operatorname{scan}\left(0, 1\right)\right) = \operatorname{singleton}\left(1\right) \land \operatorname{IsRoleBasis}\left(\operatorname{zeroUnitPair}\left(\right), \operatorname{singleton}\left(1\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.zero_role_among_nonzero_roles_is_skipped` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a two-role family containing zero and one, the zero vector is skipped and the nonzero singleton is a basis for all available roles.

**Theorem 1.18 (Greedy set cover can be suboptimal).**

$$\operatorname{uniqueLargestFirst}\left(A\right) = 0 \land \operatorname{greedyCoverSize}\left(U, A\right) = 3 \land \operatorname{optimalCoverSize}\left(U, A\right) = 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.greedy_set_cover_can_be_suboptimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unique largest set is chosen first and then needs both remaining sets, while those two sets alone already cover the ground set.

## References

- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.IsRoleBasis`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.IsSetCover`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.empty_role_scan_degenerate`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.equal_cost_role_bases_have_equal_total`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.exhaustive_scan_is_necessary`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.greedyRoleScan`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.greedyRoleScanFrom`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.greedy_role_scan_is_minimum_cost_basis`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.greedy_set_cover_can_be_suboptimal`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.linearRoleMatroid`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.linearRoleMatroid_indep_iff`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.linearRoleMatroid_isBase_iff`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.negative_costs_preserve_greedy_optimality`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.setCoverExample`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.singleton_nonzero_role_is_selected`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.singleton_zero_role_is_skipped`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.sorted_scan_is_necessary`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis.zero_role_among_nonzero_roles_is_skipped`
