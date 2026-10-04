# FirstZeroRecursion

## Abstract

Exact first-zero necessity and bounded constructive sufficiency on actual prefix cells.

**Theorem 1.1 (Every successful prefix subtree satisfies the first-zero recursion).**

$$\forall k: \mathbb{N}, m: \mathbb{N}, ell: \operatorname{Bool}, Y: \operatorname{Type}, f: \operatorname{Option}(\operatorname{LiveRecord}(k)) \to Y, v: \operatorname{ZMod}(2), h: \mathbb{N}, t: \mathbb{N}, u: \operatorname{ZMod}(2), S: \operatorname{Set}(\operatorname{ZMod}(k+1)), n: \mathbb{N}, ((((2 \leq k) \land (1 \leq m) \land (h+t \cdot m = k) \land (0 < h) \land (\operatorname{Nonempty}(S))) \land (\operatorname{BoundedReachStrategy}(\operatorname{acquisitionSystem}(k,m,ell,\operatorname{Option}(\operatorname{LiveRecord}(k))),\operatorname{targetGoal}(f),n,\operatorname{prefixCell}(k,m,t,h,v,u,S)))) \implies (\operatorname{FirstZeroCriterion}(k,m,f,v,t,h,S)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstZeroRecursion.first_zero_necessity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k>=2, m>=1, either alphabet, arbitrary label type Y and target on optional LiveRecord, initial value v, positive h and natural t with h+tm=k, arbitrary common current value u, nonempty ambient phase set S and finite horizon n, a native successful strategy at prefixCell(k,m,t,h,v,u,S) implies FirstZeroCriterion(k,m,f,v,t,h,S). The cell contains exactly the initial (v,phi,s) and current (u,phi+tm,s+tm) pairs with phi in S and s<h. ClearingCondition requires one common ORIGINAL label on all phases and tails in h-a<=s<h, and a separate common label on each phase's s<h-a fiber. The criterion is true for empty S. Otherwise it selects a<m and a<h satisfying ClearingCondition, or, only when h>m, requires rejection constancy and the criterion at every nonempty incrementChild. The induction covers stopping, all-one blocks, every locally legal first-zero block and internally illegal blocks. Each recursive child is proved equal to its actual endpoint reply fiber in both directions. This theorem is necessity; recursive sufficiency and the whole source theorem's uniform cost are separate obligations.

**Theorem 1.2 (Literal fixed archives decode endpoint subgroup phase).**

$$\forall k: \mathbb{N}, m: \mathbb{N}, ell: \operatorname{Bool}, (((2 \leq k) \land (1 \leq m)) \implies (\exists actions: \operatorname{List}(\operatorname{AllowedBlock}(k,m,ell)), ((\operatorname{length}(actions) = \operatorname{phaseCost}(k,m)) \land (\forall v1: \operatorname{ZMod}(2), v2: \operatorname{ZMod}(2), phi1: \operatorname{ZMod}(k+1), phi2: \operatorname{ZMod}(k+1), s1: \mathbb{N}, s2: \mathbb{N}, (((s1 < k) \land (s2 < k) \land (\operatorname{divides}(\operatorname{gcd}(m,k+1),\operatorname{val}(phi1))) \land (\operatorname{divides}(\operatorname{gcd}(m,k+1),\operatorname{val}(phi2))) \land (v1 = v2) \land (\operatorname{fixedBlockArchive}(actions,\operatorname{some}(v1,phi1,s1)) = \operatorname{fixedBlockArchive}(actions,\operatorname{some}(v2,phi2,s2)))) \implies (phi1 = phi2))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstZeroRecursion.safe_phase_protocol` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k>=2, m>=1 and either alphabet there exists a fixed list of allowed complete blocks of length phaseCost(k,m). For any two live records with tails below k, phases in P, and equal scalar values, equality of the two actual fixedBlockArchive lists implies equal phases. phaseCost is zero for p=1, p-1 for m>=2 and p>1, 2T for m=1 with odd T, and 2T+1 for m=1 with even T. The lists are respectively empty, repeated isolatedProbe(m,j), the single-bit pairs (01)^T, and (01)^(T/2) 0 (01)^(T/2). Initial scalar equality is the free endpoint baseline. Prefix execution connects each sample in the list to the literal phase recovery supplier. The exported conclusion is exact length and phase separation at equal visible baselines; it does not add a separate universal survival conjunct or a total decoder. No clock reading is assumed.

**Theorem 1.3 (First-zero recursion constructs an actual bounded strategy).**

$$\forall k: \mathbb{N}, m: \mathbb{N}, ell: \operatorname{Bool}, Y: \operatorname{Type}, f: \operatorname{Option}(\operatorname{LiveRecord}(k)) \to Y, v: \operatorname{ZMod}(2), h: \mathbb{N}, t: \mathbb{N}, u: \operatorname{ZMod}(2), S: \operatorname{Set}(\operatorname{ZMod}(k+1)), ((((2 \leq k) \land (1 \leq m) \land (h+t \cdot m = k) \land (0 < h) \land (\operatorname{Nonempty}(S))) \land (\forall phi: \operatorname{ZMod}(k+1), ((phi \in S) \implies (\operatorname{divides}(\operatorname{gcd}(m,k+1),\operatorname{val}(phi))))) \land (\operatorname{FirstZeroCriterion}(k,m,f,v,t,h,S))) \implies (\operatorname{BoundedReachStrategy}(\operatorname{acquisitionSystem}(k,m,ell,\operatorname{Option}(\operatorname{LiveRecord}(k))),\operatorname{targetGoal}(f),\operatorname{prefixBudget}(k,m,h),\operatorname{prefixCell}(k,m,t,h,v,u,S))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstZeroRecursion.first_zero_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary Y and f on Option LiveRecord, k>=2, m>=1, either alphabet, h>0, h+t*m=k, nonempty S contained in P, and any common current value u, FirstZeroCriterion implies a native bounded strategy on prefixCell(k,m,t,h,v,u,S). Its horizon is floor((h-1)/m)+1+phaseCost(k,m). A clearing witness a issues exactly 1^a 0^(m-a). Rejection cells stop with their common ORIGINAL target. Surviving cells decode the actual protocol-start phase and cancel the known (t+1)*m shift before applying each initial-phase label constancy condition. Empty R_0 supplies no label witness. A recursive witness issues U and constructs a continuation on each attained reply cell, proving its exact equality with the smaller prefixCell. The recursion decreases h by m and its child horizon plus one equals the parent horizon. The goal retains initial sources through every transition; there is no decidable equality premise on Y.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstZeroRecursion.first_zero_necessity`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstZeroRecursion.first_zero_sufficiency`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstZeroRecursion.safe_phase_protocol`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells](EndpointCells.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery](PhaseRecovery.md)
