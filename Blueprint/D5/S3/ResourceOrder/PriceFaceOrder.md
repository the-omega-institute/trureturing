# Order and Incomparability in the Price Face

## Abstract

The price face carries a genuine two-direction preorder of tax receipts.

The frozen PriceFace module introduced the cost-profile, physical-cost, and tax-receipt layers together with the priceFace set, but it proved nothing. This module supplies its first theorems and closes the open left by the frozen doc comment, which says verbatim, "This definition does not assert that the face has more than one independent cost direction." The concrete face has two independent directions.

The new preorder instances reuse the frozen module's LE relation. They add only reflexivity and transitivity, so the symbol <= has the same meaning in both modules; the structure is extended rather than shadowed. At the profile layer, eventual domination compares all sufficiently large scales.

The order is proved to be a preorder rather than merely described as one. The constant-zero profile and the profile that spikes to one at scale zero dominate each other eventually, although they are unequal. The concrete trade receipts then exchange forward time against forward space, yielding two distinct incomparable minimal elements of the price face.

The reachability lemmas make the set-theoretic boundary explicit: membership in priceFace supplies a valid witness, and the face is empty when no valid witness exists. Every authored display below is legal because the current projector has no pinned projectable statement fixture for these declarations; construction records a ProjectionGap for each one.

**Theorem 1.1 (Eventual domination of cost profiles is transitive).**

$$\forall Cost \in \operatorname{Type}, \forall left, middle, right \in \operatorname{CostProfile}(Cost), left\leq middle \Rightarrow middle\leq right \Rightarrow left\leq right$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceFaceOrder.costProfile_preorder_trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every preordered cost type, eventual domination composes: a profile no greater than a second profile, followed by the second no greater than a third, makes the first no greater than the third.

**Theorem 1.2 (The physical-cost order is transitive).**

$$\forall Cost \in \operatorname{Type}, \forall left, middle, right \in \operatorname{PhysicalCosts}(Cost), left\leq middle \Rightarrow middle\leq right \Rightarrow left\leq right$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceFaceOrder.physicalCosts_preorder_trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four componentwise comparisons of forward time, forward space, reverse time, and reverse space compose independently. Their conjunction is exactly the transitivity law for PhysicalCosts.

**Theorem 1.3 (The componentwise tax-receipt order is transitive).**

$$\forall AlgorithmCost, RateCost, PhysicalCost, HeatCost \in \operatorname{Type}, \forall left, middle, right \in \operatorname{TaxReceipt}(AlgorithmCost, RateCost, PhysicalCost, HeatCost) \Rightarrow left \leq middle \Rightarrow middle \leq right \Rightarrow left \leq right$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceFaceOrder.taxReceipt_preorder_trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the receipt layer, the algorithm costs, rate, four physical profiles, and heat cost are ordered componentwise. Transitivity is obtained by composing each field and therefore introduces no new relation beyond the frozen LE.

**Lemma 1.4 (The forward trade receipt is not below the reverse trade receipt).**

$$\neg(\operatorname{tradeReceipt}(true) \leq \operatorname{tradeReceipt}(false))$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceFaceOrder.trade_true_not_le_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The receipt with the forward-time and forward-space assignment exchanged in the true branch cannot be below the false branch: its forward-space profile would require the constantly-one function to be eventually no greater than the constantly-zero function.

**Lemma 1.5 (The reverse trade receipt is not below the forward trade receipt).**

$$\neg(\operatorname{tradeReceipt}(false) \leq \operatorname{tradeReceipt}(true))$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceFaceOrder.trade_false_not_le_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The converse comparison fails for the dual reason: the reverse branch would force its constantly-one forward-time profile below the constantly-zero profile. Thus neither trade can be purchased at a weakly lower receipt.

**Theorem 1.6 (Eventual cost-profile domination is not antisymmetric).**

$$zeroProfile \leq spikeProfile \land spikeProfile \leq zeroProfile \land zeroProfile \neq spikeProfile$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceFaceOrder.costProfile_eventual_order_not_antisymmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constantly-zero profile and the profile that equals one only at scale zero dominate each other eventually, but evaluation at scale zero separates them. This explicit witness proves that the eventual order is a preorder and not a partial order.

**Theorem 1.7 (The concrete trade face has two distinct incomparable minima).**

$$\operatorname{tradeReceipt}(true) \in tradeFace \land \operatorname{tradeReceipt}(false) \in tradeFace \land \operatorname{tradeReceipt}(true) \neq \operatorname{tradeReceipt}(false) \land \neg(\operatorname{tradeReceipt}(true) \leq \operatorname{tradeReceipt}(false)) \land \neg(\operatorname{tradeReceipt}(false) \leq \operatorname{tradeReceipt}(true))$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceFaceOrder.trade_face_two_incomparable_minima` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both concrete receipts are reachable from valid Boolean witnesses and are minimal among the reachable receipts. They are distinct because their forward time profiles differ, while the preceding two lemmas prove mutual incomparability. A face with one minimal element would be a point; this pair earns the name price face by exhibiting two independent cost directions.

**Theorem 1.8 (Membership in the price face implies reachability by a valid witness).**

$$\forall Object, Witness, AlgorithmCost, RateCost, PhysicalCost, HeatCost \in \operatorname{Type}, \forall candidate \in \operatorname{TaxReceipt}(AlgorithmCost, RateCost, PhysicalCost, HeatCost), candidate \in \operatorname{priceFace}(validWitness, receipt, left, right) \Rightarrow \exists witness, validWitness(witness, left, right) \land receipt(witness)= candidate$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceFaceOrder.priceFace_mem_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first coordinate of the Minimal predicate is exactly the reachability condition. Consequently, any candidate lying in priceFace comes from some witness accepted by the supplied validity predicate.

**Theorem 1.9 (The price face is empty when no valid witness exists).**

$$\neg\exists witness, validWitness(witness, left, right) \Rightarrow \operatorname{priceFace}(validWitness, receipt, left, right) = \emptyset$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceFaceOrder.priceFace_eq_empty_of_no_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the validity predicate has no witness for the two objects, the preceding reachability result rules out every possible member of priceFace. Set extensionality then identifies the face with the empty set.

## References

- Truth anchor: `D5/S3/ResourceOrder/PriceFaceOrder.costProfile_eventual_order_not_antisymmetric`
- Truth anchor: `D5/S3/ResourceOrder/PriceFaceOrder.costProfile_preorder_trans`
- Truth anchor: `D5/S3/ResourceOrder/PriceFaceOrder.physicalCosts_preorder_trans`
- Truth anchor: `D5/S3/ResourceOrder/PriceFaceOrder.priceFace_eq_empty_of_no_valid`
- Truth anchor: `D5/S3/ResourceOrder/PriceFaceOrder.priceFace_mem_reachable`
- Truth anchor: `D5/S3/ResourceOrder/PriceFaceOrder.taxReceipt_preorder_trans`
- Truth anchor: `D5/S3/ResourceOrder/PriceFaceOrder.trade_face_two_incomparable_minima`
- Truth anchor: `D5/S3/ResourceOrder/PriceFaceOrder.trade_false_not_le_true`
- Truth anchor: `D5/S3/ResourceOrder/PriceFaceOrder.trade_true_not_le_false`
- Dependency: [D5/S3/Resource/PriceFace](../Resource/PriceFace.md)
