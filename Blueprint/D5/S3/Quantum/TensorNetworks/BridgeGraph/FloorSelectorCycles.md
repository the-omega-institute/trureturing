# FloorSelectorCycles

## Abstract

FloorSelectorCycles supplies the width-three bridge max-flow proof.

Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.

**Definition 1.1 (jump).**

$$\forall (\rho : \mathbb{Q}) (n : \mathbb{Z}) , \operatorname{FloorSelectorCycles.jump} \rho n = (\operatorname{Int.ceil}\left((\operatorname{Coe.coe}\left(n + 1\right)) \cdot \rho\right) - \operatorname{Int.ceil}\left((\operatorname{Coe.coe}\left(n\right)) \cdot \rho\right))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.jump` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

jump is the difference between consecutive ceilings of n*ρ; jump_zero_or_one bounds its values for slopes between zero and one, allowing it to represent selector events.

**Theorem 1.2 (jump_zero_or_one).**

$$\forall \{\rho : \mathbb{Q}\} , 0 \leq \rho \to \rho \leq 1 \to \forall (n : \mathbb{Z}) , \operatorname{FloorSelectorCycles.jump} \rho n = 0 \lor \operatorname{FloorSelectorCycles.jump} \rho n = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.jump_zero_or_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 ≤ ρ ≤ 1, every ceiling increment is zero or one; CyclicResolvent.forward_supported_zero applies this to the input and output slopes in the balanced-cycle recurrence.

**Theorem 1.3 (opposite_direction_excess).**

$$\forall \{\rho_{I} \rho_{O} : \mathbb{Q}\} , \rho_{I} \leq \rho_{O} \to \forall (phaseI phaseO : \mathbb{Z}) (len : \mathbb{N}) , \sum_{t \in \operatorname{Finset.range} len} ((\operatorname{FloorSelectorCycles.jump} \rho_{I} (phaseI + (\operatorname{Coe.coe}\left(t\right))) - \operatorname{FloorSelectorCycles.jump} \rho_{O} (phaseO - (\operatorname{Coe.coe}\left(t\right))))) \leq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.opposite_direction_excess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When ρI ≤ ρO, the input ceiling increments along a forward interval exceed the output increments along a backward interval by at most one; CyclicResolvent.forward_supported_zero uses this as the interval balance inequality.

**Theorem 1.4 (jump_one_iff_fin_selector).**

$$\forall (A B : \mathbb{N}) , 0 < B \to B \leq A \to \forall (n : Fin A) , \operatorname{FloorSelectorCycles.jump} (((B:\mathbb{Q})) \operatorname{HDiv.hDiv} ((A:\mathbb{Q}))) (((\operatorname{val}\left(n\right)):\mathbb{Z})) = 1 \iff \exists (k : Fin B) , (\operatorname{val}\left(n\right)) = (\operatorname{val}\left(k\right)) \cdot A \operatorname{HDiv.hDiv} B$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.jump_one_iff_fin_selector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < B ≤ A, a ceiling increment at n in Fin A equals one exactly when n is one of the positions floor(k*A/B) with k in Fin B; CyclicResolvent.forward_supported_zero uses this equivalence to express coordinate support as selector events.

**Theorem 1.5 (monodromy_forces_zero).**

$$\forall (\mu z : \mathbb{Q}) , \mu < 1 \to z = \mu \cdot z \to z = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.monodromy_forces_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational value fixed by multiplication by μ < 1 must vanish; balanced_cycle_zero applies this after propagating a coordinate around a full period.

**Theorem 1.6 (half_pow_lt_one).**

$$\forall \{n : \mathbb{N}\} , 0 < n \to (1 \operatorname{HDiv.hDiv} 2)^{n} < 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.half_pow_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive power of the rational number 1/2 is strictly below one; tensor_edge_product_lt_one uses this to bound the product of weights around the tensor cycle.

**Theorem 1.7 (recurrence_product_bounded).**

$$\forall (z f : \mathbb{N} \to \mathbb{Q}) (L : \mathbb{N}) , (\forall n < L , z (n + 1) = f n \cdot z n) \to z L = (\prod_{t \in \operatorname{Finset.range} L} (f t)) \cdot z 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.recurrence_product_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterating a multiplicative recurrence over L steps multiplies the initial value by the product of its L factors; balanced_cycle_zero uses this identity to compare a coordinate with its value one period later.

**Theorem 1.8 (balanced_cycle_zero).**

$$\forall (i o : \mathbb{Z} \to \mathbb{Z}) (z c : \mathbb{Z} \to \mathbb{Q}) , (\forall (n : \mathbb{Z}) , i n = 0 \lor i n = 1) \to (\forall (n : \mathbb{Z}) , o n = 0 \lor o n = 1) \to (\forall (n : \mathbb{Z}) , i n = o n \to z n = c n \cdot z (n - 1)) \to (\forall (n : \mathbb{Z}) , c n \neq 0) \to (\forall (n : \mathbb{Z}) , i n = 0 \to o n = 1 \to z n = 0 \land z (n - 1) = 0) \to (\forall (a : \mathbb{Z}) (len : \mathbb{N}) , \sum_{t \in \operatorname{Finset.range} len} ((i (a + (\operatorname{Coe.coe}\left(t\right))) - o (a + (\operatorname{Coe.coe}\left(t\right))))) \leq 1) \to \forall (L : \mathbb{N}) , 0 < L \to (\forall (n : \mathbb{Z}) , z (n + (\operatorname{Coe.coe}\left(L\right))) = z n) \to (\forall (a : \mathbb{Z}) , \sum_{t \in \operatorname{Finset.range} L} ((i (a + (\operatorname{Coe.coe}\left(t\right))) - o (a + (\operatorname{Coe.coe}\left(t\right))))) \leq 0) \to (\forall (a : \mathbb{Z}) , \prod_{t \in \operatorname{Finset.range} L} (c (a + (\operatorname{Coe.coe}\left(t\right)) + 1)) < 1) \to \forall (a : \mathbb{Z}) , z a = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.balanced_cycle_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the displayed recurrence and zero conditions, binary input and output sequences with interval excess at most one and nonpositive full-period excess force every periodic coordinate to vanish when each period product is below one. CyclicResolvent.shifted_recurrence_zero applies this to the supported reservoir equations.

**Theorem 1.9 (common_node_product_bound).**

$$\forall (\kappa : \mathbb{Q}) , 0 < \kappa \to \forall (o : \mathbb{Z} \to \mathbb{Z}) (w : \mathbb{Z} \to \mathbb{Q}) , (\forall (n : \mathbb{Z}) , 0 < w n) \to \forall (a : \mathbb{Z}) (L : \mathbb{N}) , \prod_{t \in \operatorname{Finset.range} L} ((if o (a + (\operatorname{Coe.coe}\left(t\right)) + 1) = 1 then \kappa \operatorname{HDiv.hDiv} (\kappa + 1) else 1) \cdot w (a + (\operatorname{Coe.coe}\left(t\right)) + 1)) \leq \prod_{t \in \operatorname{Finset.range} L} (w (a + (\operatorname{Coe.coe}\left(t\right)) + 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.common_node_product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For κ > 0 and positive weights, inserting a factor κ/(κ+1) at output events cannot increase the product of weights; CyclicResolvent.shifted_recurrence_zero uses this to preserve the strict period-product bound.

**Definition 1.10 (backward).**

$$\forall (A : \mathbb{N}) , \operatorname{FloorSelectorCycles.backward} A = (\operatorname{Matrix.submatrix} 1 ((\operatorname{CoeFun.coe}\left(finRotate A\right))) id)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.backward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

backward is the unweighted cyclic shift obtained by rotating the rows of the identity matrix; tensor_mulVec_orbit uses it to decrease the first orbit coordinate by one.

**Theorem 1.11 (backward_apply).**

$$\forall (A : \mathbb{N}) (i j : Fin A) , \operatorname{FloorSelectorCycles.backward} A i j = if (\operatorname{val}\left(j\right)) = ((\operatorname{val}\left(i\right)) + 1) \operatorname{HMod.hMod} A then 1 else 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.backward_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entry of backward at (i,j) is one exactly when j is the cyclic successor of i and is zero otherwise; tensor_mulVec_orbit uses this entry formula to isolate the preceding orbit position.

**Definition 1.12 (forwardHalf).**

$$\forall (G : \mathbb{N}) , \operatorname{FloorSelectorCycles.forwardHalf} G = ((\operatorname{Matrix.diagonal} fun (k : Fin G) \mapsto if (\operatorname{val}\left(k\right)) = 0 then 1 \operatorname{HDiv.hDiv} 2 else 1) . submatrix id (\operatorname{CoeFun.coe}\left(finRotate G\right)))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.forwardHalf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

forwardHalf is the opposite cyclic shift with weight 1/2 at row zero and weight one elsewhere; tensor_mulVec_orbit uses this weight to describe propagation in the second coordinate.

**Theorem 1.13 (forwardHalf_apply).**

$$\forall (G : \mathbb{N}) (i j : Fin G) , \operatorname{FloorSelectorCycles.forwardHalf} G i j = if (\operatorname{val}\left(j\right)) = ((\operatorname{val}\left(i\right)) + G - 1) \operatorname{HMod.hMod} G then if (\operatorname{val}\left(i\right)) = 0 then 1 \operatorname{HDiv.hDiv} 2 else 1 else 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.forwardHalf_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entry of forwardHalf at (i,j) is nonzero only when j is the cyclic predecessor of i, with weight 1/2 at i=0 and one elsewhere; tensor_mulVec_orbit uses this formula to obtain the factor edge.

**Definition 1.14 (rowSelector).**

$$\forall (A B : \mathbb{N}) , \operatorname{FloorSelectorCycles.rowSelector} A B = ((\operatorname{Matrix.submatrix} 1 \operatorname{Fin.val} fun (k : Fin B) \mapsto (\operatorname{val}\left(k\right)) \cdot A \operatorname{HDiv.hDiv} B) . transpose)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.rowSelector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rowSelector samples positions floor(k*A/B) from an A-coordinate vector into B coordinates; CyclicResolvent.input_matrix and output_matrix express the tensor input and output maps using these selectors.

**Definition 1.15 (reservoir).**

$$\forall (A G : \mathbb{N}) , \operatorname{FloorSelectorCycles.reservoir} A G = (1 + (- \operatorname{FloorSelectorCycles.backward} A) . kronecker (\operatorname{FloorSelectorCycles.forwardHalf} G))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.reservoir` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

reservoir is the identity minus the Kronecker product of the two oppositely directed cyclic shifts; CyclicResolvent.reservoir_isUnit proves its invertibility by propagating its homogeneous equation around each orbit.

**Definition 1.16 (schurMap).**

$$\forall (A B G D : \mathbb{N}) (\kappa : \mathbb{Q}) , \operatorname{FloorSelectorCycles.schurMap} A B G D \kappa = (\kappa \cdot (\operatorname{FloorSelectorCycles.rowSelector} A B) . kronecker (\operatorname{FloorSelectorCycles.rowSelector} G D) . transpose + (\operatorname{FloorSelectorCycles.rowSelector} A B) . kronecker 1 \cdot (\operatorname{FloorSelectorCycles.reservoir} A G)^{-1} \cdot \operatorname{Matrix.kronecker} 1 (\operatorname{FloorSelectorCycles.rowSelector} G D) . transpose)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.schurMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

schurMap restricts κ times the identity plus the inverse reservoir to the selected input and output coordinates; CyclicResolvent.schur_eq_restricted expresses this restriction through coordinate-insertion matrices.

**Definition 1.17 (CyclicResolventLemma).**

$$\operatorname{FloorSelectorCycles.CyclicResolventLemma} \iff (\forall (A B G D : \mathbb{N}) , 0 < B \to B \leq A \to 0 < D \to D \leq G \to \forall (\kappa : \mathbb{Q}) , 0 < \kappa \to IsUnit (\operatorname{FloorSelectorCycles.reservoir} A G) \land (A \cdot D \leq B \cdot G \to \operatorname{Function.Injective} (\operatorname{FloorSelectorCycles.schurMap} A B G D \kappa) . mulVec) \land (B \cdot G \leq A \cdot D \to \operatorname{Function.Surjective} (\operatorname{FloorSelectorCycles.schurMap} A B G D \kappa) . mulVec))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.CyclicResolventLemma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CyclicResolventLemma states invertibility of the reservoir and injectivity or surjectivity of schurMap according to the ordering of A*D and B*G, for positive ordered selector dimensions and κ > 0; CyclicResolvent.cyclic_resolvent_lemma proves these assertions.

**Definition 1.18 (index).**

$$\forall (N : \mathbb{N}) (hN : 0 < N) (s : \mathbb{Z}) , \operatorname{FloorSelectorCycles.index} N hN s = (\langle \operatorname{s.natMod} (\operatorname{Coe.coe}\left(N\right)) \rangle)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive modulus N, index maps an integer to its remainder in Fin N; orbit uses it to follow both cyclic coordinates for arbitrary integer steps.

**Theorem 1.19 (index_val_int).**

$$\forall (N : \mathbb{N}) (hN : 0 < N) (s : \mathbb{Z}) , (((\operatorname{val}\left(\operatorname{FloorSelectorCycles.index} N hN s\right)):\mathbb{Z})) = s \operatorname{HMod.hMod} ((N:\mathbb{Z}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index_val_int` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer value of index is the integer remainder modulo N; index_nat uses this equality to recover an index already in Fin N.

**Theorem 1.20 (index_nat).**

$$\forall (N : \mathbb{N}) (hN : 0 < N) (i : Fin N) , \operatorname{FloorSelectorCycles.index} N hN (((\operatorname{val}\left(i\right)):\mathbb{Z})) = i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reducing the value of an element of Fin N modulo N returns that element; CyclicResolvent.succ_pred_relation uses this to translate cyclic successor and predecessor equations into integer shifts.

**Theorem 1.21 (index_add_multiple).**

$$\forall (N : \mathbb{N}) (hN : 0 < N) (s k : \mathbb{Z}) , \operatorname{FloorSelectorCycles.index} N hN (s + k \cdot (\operatorname{Coe.coe}\left(N\right))) = \operatorname{FloorSelectorCycles.index} N hN s$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index_add_multiple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding any integer multiple of N leaves index unchanged; orbit_period applies this in both coordinates to obtain a period of A*G.

**Theorem 1.22 (index_add_one).**

$$\forall (N : \mathbb{N}) (hN : 0 < N) (s : \mathbb{Z}) , (\operatorname{val}\left(\operatorname{FloorSelectorCycles.index} N hN (s + 1)\right)) = ((\operatorname{val}\left(\operatorname{FloorSelectorCycles.index} N hN s\right)) + 1) \operatorname{HMod.hMod} N$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index_add_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Increasing the integer argument of index by one advances its value by one modulo N; tensor_mulVec_orbit uses this to identify the first-coordinate shift.

**Theorem 1.23 (index_sub_one).**

$$\forall (N : \mathbb{N}) (hN : 0 < N) (s : \mathbb{Z}) , (\operatorname{val}\left(\operatorname{FloorSelectorCycles.index} N hN (s - 1)\right)) = ((\operatorname{val}\left(\operatorname{FloorSelectorCycles.index} N hN s\right)) + N - 1) \operatorname{HMod.hMod} N$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decreasing the integer argument of index by one gives its cyclic predecessor; tensor_mulVec_orbit uses this to identify the second-coordinate shift.

**Definition 1.24 (orbit).**

$$\forall (A G : \mathbb{N}) (hA : 0 < A) (hG : 0 < G) (a b s : \mathbb{Z}) , \operatorname{FloorSelectorCycles.orbit} A G hA hG a b s = ((\operatorname{FloorSelectorCycles.index} A hA (a - s) , \operatorname{FloorSelectorCycles.index} G hG (b + s)))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.orbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

orbit follows the positions (a-s modulo A,b+s modulo G), with the two coordinates moving in opposite directions; CyclicResolvent.reservoir_mulVec_orbit expresses the reservoir equation along this orbit.

**Definition 1.25 (edge).**

$$\forall (G : \mathbb{N}) (hG : 0 < G) (s : \mathbb{Z}) , \operatorname{FloorSelectorCycles.edge} G hG s = (if (\operatorname{val}\left(\operatorname{FloorSelectorCycles.index} G hG s\right)) = 0 then 1 \operatorname{HDiv.hDiv} 2 else 1)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

edge assigns weight 1/2 at positions divisible by G and one at all other positions; tensor_mulVec_orbit identifies it as the coefficient relating successive orbit coordinates.

**Theorem 1.26 (orbit_period).**

$$\forall (A G : \mathbb{N}) (hA : 0 < A) (hG : 0 < G) (a b s : \mathbb{Z}) , \operatorname{FloorSelectorCycles.orbit} A G hA hG a b (s + (\operatorname{Coe.coe}\left(A\right)) \cdot (\operatorname{Coe.coe}\left(G\right))) = \operatorname{FloorSelectorCycles.orbit} A G hA hG a b s$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.orbit_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive A and G, shifting the orbit parameter by A*G returns the same pair of coordinates; CyclicResolvent.reservoir_isUnit uses this periodicity to close the homogeneous recurrence.

**Theorem 1.27 (edge_pos).**

$$\forall (G : \mathbb{N}) (hG : 0 < G) (s : \mathbb{Z}) , 0 < \operatorname{FloorSelectorCycles.edge} G hG s$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.edge_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every edge weight is strictly positive; CyclicResolvent.forward_supported_zero uses this to satisfy the nonzero propagation condition in the balanced-cycle argument.

**Theorem 1.28 (tensor_mulVec_orbit).**

$$\forall (A G : \mathbb{N}) (hA : 0 < A) (hG : 0 < G) (z : Fin A \times Fin G \to \mathbb{Q}) (a b s : \mathbb{Z}) , ((\operatorname{FloorSelectorCycles.backward} A) . kronecker (\operatorname{FloorSelectorCycles.forwardHalf} G)) . mulVec z (\operatorname{FloorSelectorCycles.orbit} A G hA hG a b s) = \operatorname{FloorSelectorCycles.edge} G hG (b + s) \cdot z (\operatorname{FloorSelectorCycles.orbit} A G hA hG a b (s - 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.tensor_mulVec_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Kronecker shift sends the value at an orbit position to edge times the value at the preceding position; CyclicResolvent.reservoir_mulVec_orbit subtracts this contribution from the identity term.

**Theorem 1.29 (whole_tensor_excess).**

$$\forall (A B G D : \mathbb{N}) , 0 < A \to 0 < G \to \forall (phaseI phaseO : \mathbb{Z}) , \sum_{t \in \operatorname{Finset.range} (A \cdot G)} ((\operatorname{FloorSelectorCycles.jump} ((\operatorname{Coe.coe}\left(D\right)) \operatorname{HDiv.hDiv} (\operatorname{Coe.coe}\left(G\right))) (phaseI + (\operatorname{Coe.coe}\left(t\right))) - \operatorname{FloorSelectorCycles.jump} ((\operatorname{Coe.coe}\left(B\right)) \operatorname{HDiv.hDiv} (\operatorname{Coe.coe}\left(A\right))) (phaseO - (\operatorname{Coe.coe}\left(t\right))))) = (\operatorname{Coe.coe}\left(A \cdot D\right)) - (\operatorname{Coe.coe}\left(G \cdot B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.whole_tensor_excess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over A*G steps with A,G > 0, the difference between the input and output event counts is exactly A*D-G*B; CyclicResolvent.forward_supported_zero uses the dimension ordering to make this full-period excess nonpositive.

**Theorem 1.30 (jump_index).**

$$\forall (A B : \mathbb{N}) (hA : 0 < A) (s : \mathbb{Z}) , \operatorname{FloorSelectorCycles.jump} (((B:\mathbb{Q})) \operatorname{HDiv.hDiv} ((A:\mathbb{Q}))) (((\operatorname{val}\left(\operatorname{FloorSelectorCycles.index} A hA s\right)):\mathbb{Z})) = \operatorname{FloorSelectorCycles.jump} (((B:\mathbb{Q})) \operatorname{HDiv.hDiv} ((A:\mathbb{Q}))) s$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.jump_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive A, reducing an integer modulo A does not change the ceiling increment of slope B/A; CyclicResolvent.forward_supported_zero uses this to identify selector events along integer orbit parameters.

**Theorem 1.31 (edge_product).**

$$\forall (G M : \mathbb{N}) (hG : 0 < G) (phase : \mathbb{Z}) , \prod_{t \in \operatorname{Finset.range} (M \cdot G)} (\operatorname{FloorSelectorCycles.edge} G hG (phase + (\operatorname{Coe.coe}\left(t\right)))) = (1 \operatorname{HDiv.hDiv} 2)^{M}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.edge_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over M*G consecutive positions with G > 0, the product of edge weights is (1/2)^M, independently of the starting phase; tensor_edge_product_lt_one uses this formula over a tensor period.

**Theorem 1.32 (tensor_edge_product_lt_one).**

$$\forall (A G : \mathbb{N}) , 0 < A \to \forall (hG : 0 < G) (phase : \mathbb{Z}) , \prod_{t \in \operatorname{Finset.range} (A \cdot G)} (\operatorname{FloorSelectorCycles.edge} G hG (phase + (\operatorname{Coe.coe}\left(t\right)) + 1)) < 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.tensor_edge_product_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive A and G, the product of edge weights over A*G consecutive orbit steps is strictly below one; CyclicResolvent.reservoir_isUnit uses this contraction to force its homogeneous kernel to vanish.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.CyclicResolventLemma`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.backward`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.backward_apply`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.balanced_cycle_zero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.common_node_product_bound`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.edge`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.edge_pos`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.edge_product`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.forwardHalf`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.forwardHalf_apply`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.half_pow_lt_one`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index_add_multiple`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index_add_one`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index_nat`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index_sub_one`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.index_val_int`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.jump`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.jump_index`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.jump_one_iff_fin_selector`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.jump_zero_or_one`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.monodromy_forces_zero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.opposite_direction_excess`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.orbit`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.orbit_period`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.recurrence_product_bounded`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.reservoir`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.rowSelector`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.schurMap`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.tensor_edge_product_lt_one`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.tensor_mulVec_orbit`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles.whole_tensor_excess`
