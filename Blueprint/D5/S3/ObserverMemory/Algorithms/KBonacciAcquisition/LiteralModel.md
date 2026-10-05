# LiteralModel

## Abstract

Original KBonacci weights, literal bit execution, and joint actual-history realization.

Fix an original order k at least two. LiveRecord has value in ZMod 2, ambient phase in ZMod (k+1), and a natural tail. The legal-tail premise is tail below k. Rejection is none and is absorbing. A false bit advances phase and clears tail; a true bit adds the coefficient at the old phase and increments tail, rejecting when the new tail reaches k. coefficient is one precisely at phases zero and minus one, and zero elsewhere. runBits uses the native chronological runWord. endpointReading offers only the resulting value or rejection after the entire supplied word.

**Theorem 1.1 (Old-tail scanning and literal endpoint updates agree).**

$$\forall k: \mathbb{N}, n: \mathbb{N}, w: \operatorname{Fin}(n) \to \operatorname{Bool}, v: \operatorname{ZMod}(2), phi: \operatorname{ZMod}(k+1), s: \mathbb{N}, (((2 \leq k) \land (s < k)) \implies ((\operatorname{runBits}(k,w,\operatorname{some}(v,phi,s)) = \operatorname{if}(\operatorname{runAdmissible}(k-1,k-1-s,n,w) = \operatorname{true},\operatorname{some}(v+\operatorname{wordIncrement}(k,phi,w),phi+n,\operatorname{tailAfter}(s,w)),\operatorname{none})) \land ((\operatorname{runAdmissible}(k-1,k-1-s,n,w) = \operatorname{true}) \implies (\operatorname{tailAfter}(s,w) < k))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel.literal_block_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quantify over every natural k at least two, every natural n, every Boolean word w on Fin n, every value v in ZMod 2, every ambient phase phi in ZMod (k+1), and every natural s below k. accepted(w) means the native runAdmissible scanner with maxTrue=k-1 and fuel=k-1-s returns true. scanResult is none on failure, and otherwise is the live record (v+wordIncrement(k,phi,w),phi+n,tailAfter(s,w)). wordIncrement sums the coefficient at each actual position whose bit is true. tailAfter performs the chronological tail updates. Execution equals scanResult, and acceptance implies tailAfter(s,w) below k. No bit within a block is added to the observation interface.

**Theorem 1.2 (One actual legal word realizes all live coordinates).**

$$\forall k: \mathbb{N}, m: \mathbb{N}, v: \operatorname{ZMod}(2), phi: \operatorname{ZMod}(k+1), s: \mathbb{N}, (((2 \leq k) \land (1 \leq m) \land (s < k) \land (\operatorname{divides}(\operatorname{gcd}(m,k+1),\operatorname{val}(phi)))) \implies (\exists N: \mathbb{N}, w: \operatorname{Fin}(N) \to \operatorname{Bool}, ((\operatorname{divides}(m,N)) \land (\operatorname{DBonacciAdmissible}(k,N,w)) \land (\operatorname{runBits}(k,w,\operatorname{some}(0,0,0)) = \operatorname{some}(v,phi,s)) \land (\operatorname{originalWordValue}(k,w) = v) \land (\operatorname{tailAfter}(0,w) = s) \land (\forall j: \mathbb{N}, (((j+1) \cdot m \leq N) \implies (\operatorname{DBonacciAdmissible}(k,m,\lambda i: \operatorname{Fin}(m), \operatorname{w}(j \cdot m+\operatorname{val}(i)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel.joint_history_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k at least two, positive natural m, value v in ZMod 2, ambient phase phi in ZMod (k+1), and natural tail s below k, assume gcd(m,k+1) divides the natural representative phi.val. There exist one natural N and one word w on Fin N such that m divides N, w is DBonacciAdmissible, its execution from the empty record is exactly (v,phi,s), its originalWordValue is v, and tailAfter(0,w) is s. For every natural j with (j+1)m at most N, the length-m subword at positions jm through (j+1)m-1 is DBonacciAdmissible as well.

The construction applies the generalized natural CRT to the compatible residues zero modulo m and phi.val modulo k+1, then enlarges that same length. The witness is a first bit v+d, followed by N-s-1 zero bits and s one bits; d is the coefficient sum at those final s positions. The value, phase, tail and all local blocks therefore concern the same word. These statements supply live source records. Rejected-source realization, phase acquisition, the full first-zero recursion and the full adaptive acquisition iff and cost bound require their own mathematical conclusions.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel.joint_history_realization`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel.literal_block_execution`
- Dependency: [D5/S0/Tower/DBonacci/Substitution](../../../../S0/Tower/DBonacci/Substitution.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/UniformBaseGap](../../../../S0/Tower/DBonacciGeneral/UniformBaseGap.md)
- Dependency: [D5/S1/Words/ClosedRunStarts](../../../../S1/Words/ClosedRunStarts.md)
- Dependency: [D5/S3/ConceptDynamics/Control/FiniteHorizonReachability](../../../ConceptDynamics/Control/FiniteHorizonReachability.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../../Prediction/ControlledBehaviorUniversality.md)
