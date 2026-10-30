# Region Filters and Uniform Past Tails

## Abstract

A region has a native charge expression exactly when its past tail is uniform.

**Definition 1.1 (One threshold works for every position).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.Tail`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.Tail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A region is a set of integer time and integer spatial-triple pairs. TailAt R c says that, for every position p and every t,t' strictly below c, membership of (t,p) and (t',p) agrees. Tail R asserts the existence of such a single integer c. The threshold is independent of position.

**Definition 1.2 (A fixed total word computes filtered charge).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.QExpressible`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.QExpressible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

QExpressible R means that one fixed finite native one-hole word succeeds on every balanced rich input and returns the sum of signs of its selected events lying in R. The word may use arbitrary fixed balanced parameters, both binary slots, all native filters, complement and integer shifts.

**Theorem 1.3 (A total word saturates below one common time).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.total_word_saturation`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.total_word_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed native word total on all balanced rich inputs, there is an integer c such that every position p and every pair t,t' below c admit two legal inputs with equal final optional charge. Their archives have the same literal event names, order, current region and selection. Only the time of the unique selected positive event differs, from t to t'; its position is p and its source agrees. Common earlier and later archive events strictly enclose both times.

Exact total-word normalization removes temporal composition. The finite family of pulled-back causal predicates before the first product supplies finitely many target attributes and a common lower time bound. A balanced star adds a current successor for each nonempty predicate, an unselected opposite-sign twin for every current contribution, and two common inactive endpoints. Every prefix filter therefore acts synchronously. A current correspondence preserves attributes, causal order and selection, without matching inactive archive attributes. Parallel composition transports it through a disjoint sum and generated product through current-parent pairs. At the first product in either slot, the exceptional time is below every current parent time in the fixed factor, so the maximum erases it from generated attributes. An empty current factor also satisfies this argument. Every subsequent temporal-free step preserves the current correspondence. If there is no product, matching selected signs give the same conclusion directly.

**Theorem 1.4 (A shifted unit factor realizes every tail region).**

$$\forall R, c, k, X, \operatorname{TailAt}\left(R, c\right) \land k \le c - 1 \Rightarrow \operatorname{q}\left(\operatorname{tailConstruction}\left(R, k, X\right)\right) = \operatorname{regionReadout}\left(R, X\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.tail_construction_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be the canonical balanced representative with one selected positive event at time zero and position zero. Form X product T_k U and retain generated events with time n at least k+1 and (n-1,p) in R. The product time is max(t,k)+1 and its current region is an antichain, so the causal filter reads exactly R at max(t,k). When k is at most c-1, TailAt R c identifies this membership with R at the original t. The identity holds for every balanced rich input X.

**Theorem 1.5 (The exact charge-expressibility classification).**

$$\forall R, \operatorname{QExpressible}\left(R\right) \iff \operatorname{Tail}\left(R\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.q_expressible_iff_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Necessity applies total-word saturation to the expressing word. The unique selected positive point reads the two region membership bits, forcing their equality below one common c at every position. Sufficiency uses the shifted-unit construction with k=c-1. Neither direction restricts the region or the balanced input.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.QExpressible`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.Tail`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.q_expressible_iff_tail`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.tail_construction_q`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.total_word_saturation`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/CoarseObservation](CoarseObservation.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization](TotalCopyNormalization.md)
