# PhaseRecovery

## Abstract

Safe literal KBonacci phase probes for block and single-bit alphabets.

**Theorem 1.1 (Literal isolated probes supply safe endpoint samples).**

$$\forall k: \mathbb{N}, m: \mathbb{N}, j: \mathbb{N}, r: \mathbb{N}, v: \operatorname{ZMod}(2), phi: \operatorname{ZMod}(k+1), s: \mathbb{N}, (((2 \leq k) \land (1 \leq j) \land (j < m) \land (s < k)) \implies ((\operatorname{DBonacciAdmissible}(k,m,\operatorname{isolatedProbe}(m,j))) \land (\exists s0: \mathbb{N}, ((s0 < k) \land (\operatorname{iterate}(\operatorname{runBits}(k,\operatorname{isolatedProbe}(m,j)),r,\operatorname{some}(v,phi,s)) = \operatorname{some}(v+\sum_{i < r} \operatorname{coefficient}(k,phi+i \cdot m+j),phi+r \cdot m,s0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery.isolated_probe_orbit_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least two, natural m, j and r with 1<=j<m, value v, ambient phase phi and initial tail s below k, isolatedProbe(m,j) has its single true bit at j. It is locally legal. After r actual executions there is a tail s2 below k and the current record is (v+sum over i<r of coefficient(k,phi+im+j),phi+rm,s2). The orbit therefore never rejects, and adjacent complete endpoint values give the literal samples coefficient(k,phi+im+j). This supplies the execution and safety part of the multi-bit phase protocol. It does not by itself prove phase recovery from p-1 samples, the single-bit odd/even protocols, or the full acquisition criterion and bound.

**Theorem 1.2 (The odd-period single-bit protocol recovers the initial phase).**

$$\forall k: \mathbb{N}, v1: \operatorname{ZMod}(2), v2: \operatorname{ZMod}(2), phi1: \operatorname{ZMod}(k+1), phi2: \operatorname{ZMod}(k+1), s1: \mathbb{N}, s2: \mathbb{N}, (((2 \leq k) \land (\operatorname{Odd}(k+1)) \land (s1 < k) \land (s2 < k)) \implies ((\forall r: \mathbb{N}, (\exists s0: \mathbb{N}, ((s0 < k) \land (\operatorname{alternatingBitOrbit}(k,r,\operatorname{some}(v1,phi1,s1)) = \operatorname{some}(v1+\sum_{i < r} \operatorname{coefficient}(k,phi1+i \cdot 2+1),phi1+r \cdot 2,s0))))) \land ((\forall r: \mathbb{N}, ((r \leq k+1) \implies (\operatorname{endpointReading}(\operatorname{alternatingBitOrbit}(k,r,\operatorname{some}(v1,phi1,s1))) = \operatorname{endpointReading}(\operatorname{alternatingBitOrbit}(k,r,\operatorname{some}(v2,phi2,s2)))))) \implies (phi1 = phi2))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery.odd_single_bit_phase_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least two with odd T=k+1, every two values in ZMod 2, ambient phases phi1 and phi2, and initial tails s1 and s2 below k, alternatingBitOrbit literally issues a complete zero bit block followed by a complete one bit block in each pair. For every number r of pairs the first source survives with value v1 plus the sum over i<r of coefficient(k,phi1+2i+1), phase phi1+2r and a tail below k. If the actual endpoint readings of the two sources agree after every r from zero through T pairs, their initial phases are equal. The sampled offsets cover every residue because two is a unit modulo odd T. Zero endpoints are also available under the single-bit alphabet; the implication already uses only the pair endpoints. T pairs contain 2T actual single-bit actions. This theorem supplies the odd-period phase recovery case. The even-period protocol, the p-1 sample argument for wider blocks, and the overall acquisition bound are separate obligations.

**Theorem 1.3 (The even-period single-bit protocol recovers the initial phase).**

$$\forall k: \mathbb{N}, v1: \operatorname{ZMod}(2), v2: \operatorname{ZMod}(2), phi1: \operatorname{ZMod}(k+1), phi2: \operatorname{ZMod}(k+1), s1: \mathbb{N}, s2: \mathbb{N}, (((2 \leq k) \land (\operatorname{Even}(k+1)) \land (s1 < k) \land (s2 < k)) \implies ((\forall r: \mathbb{N}, (\exists value: \operatorname{ZMod}(2), s0: \mathbb{N}, ((s0 < k) \land (\operatorname{evenSingleBitOrbit}(k,r,\operatorname{some}(v1,phi1,s1)) = \operatorname{some}(value,phi1+1+r \cdot 2,s0))))) \land ((\forall r: \mathbb{N}, ((r \leq (k+1)/2) \implies (\operatorname{endpointReading}(\operatorname{alternatingBitOrbit}(k,r,\operatorname{some}(v1,phi1,s1))) = \operatorname{endpointReading}(\operatorname{alternatingBitOrbit}(k,r,\operatorname{some}(v2,phi2,s2)))))) \implies ((\forall r: \mathbb{N}, ((r \leq (k+1)/2) \implies (\operatorname{endpointReading}(\operatorname{evenSingleBitOrbit}(k,r,\operatorname{some}(v1,phi1,s1))) = \operatorname{endpointReading}(\operatorname{evenSingleBitOrbit}(k,r,\operatorname{some}(v2,phi2,s2)))))) \implies (phi1 = phi2)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery.even_single_bit_phase_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k>=2 with even T=k+1, arbitrary initial scalar values and ambient phases, and two initial tails below k, the literal single-bit protocol is (01)^(T/2), then a zero, then (01)^(T/2). Its second half survives for every number r of pairs with phase phi1+1+2r and a tail below k. Equality of the two sources' actual endpoints after every r from zero through T/2 in each half implies equality of their INITIAL phases. Differences of adjacent pair endpoints give the odd and even coefficient offsets, including offset zero at the final even sample. The protocol uses 2T+1 complete single-bit actions; it reads no hidden clock or unread bit. Target decoder and global cost integration belong to the full acquisition construction.

**Theorem 1.4 (The safe p-minus-one block archive recovers endpoint subgroup phase).**

$$\forall k: \mathbb{N}, m: \mathbb{N}, v1: \operatorname{ZMod}(2), v2: \operatorname{ZMod}(2), phi1: \operatorname{ZMod}(k+1), phi2: \operatorname{ZMod}(k+1), s1: \mathbb{N}, s2: \mathbb{N}, (((2 \leq k) \land (2 \leq m) \land (s1 < k) \land (s2 < k) \land (\operatorname{divides}(\operatorname{gcd}(m,k+1),\operatorname{val}(phi1))) \land (\operatorname{divides}(\operatorname{gcd}(m,k+1),\operatorname{val}(phi2)))) \implies ((\operatorname{DBonacciAdmissible}(k,m,\operatorname{isolatedProbe}(m,\operatorname{phaseProbeOffset}(k,m)))) \land (\forall r: \mathbb{N}, (\exists value: \operatorname{ZMod}(2), phi: \operatorname{ZMod}(k+1), s0: \mathbb{N}, ((s0 < k) \land (\operatorname{iterate}(\operatorname{runBits}(k,\operatorname{isolatedProbe}(m,\operatorname{phaseProbeOffset}(k,m))),r,\operatorname{some}(v1,phi1,s1)) = \operatorname{some}(value,phi,s0))))) \land ((\forall r: \mathbb{N}, ((r \leq (k+1)/\operatorname{gcd}(m,k+1)-1) \implies (\operatorname{endpointReading}(\operatorname{iterate}(\operatorname{runBits}(k,\operatorname{isolatedProbe}(m,\operatorname{phaseProbeOffset}(k,m))),r,\operatorname{some}(v1,phi1,s1))) = \operatorname{endpointReading}(\operatorname{iterate}(\operatorname{runBits}(k,\operatorname{isolatedProbe}(m,\operatorname{phaseProbeOffset}(k,m))),r,\operatorname{some}(v2,phi2,s2)))))) \implies (phi1 = phi2))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery.safe_block_phase_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k>=2 and m>=2, set g=gcd(m,k+1), p=(k+1)/g and j=1 if g=1, otherwise j=g-1. For arbitrary values, ambient phases whose natural representatives are divisible by g, and old tails below k, isolatedProbe(m,j) is locally legal and every repeated execution remains live. Equal endpoint readings after every r from zero through p-1 imply equality of the INITIAL phases. When p=1 each phase is zero, so no block is needed. Otherwise the proof recovers the one omitted sample using invariance of a complete cycle sum under rotation of the same endpoint subgroup. For g>=2 the sampled coset has one coefficient support position; for g=1 full translated coefficient equality forces the phase shift to vanish. No mod-two nonzero interpretation of the integer total two is used, and no unknown initial length is read.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery.even_single_bit_phase_recovery`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery.isolated_probe_orbit_exact`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery.odd_single_bit_phase_recovery`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery.safe_block_phase_recovery`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel](LiteralModel.md)
