# Excluding binary Singleton attainment at length eight or greater

## Abstract

Binary entanglement-assisted Singleton attainment is impossible at length eight or greater.

**Definition 1.1 (A code at length at least eight with at most three zeros outside the radical).**

Lean statement: `D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.claim`

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binary symplectic code has dimension eight and its radical has dimension four. Every word outside the radical vanishes on at most three sites, where vanishing means that both binary coordinates are zero.

**Theorem 1.2 (Exclusion at every length from eight onward).**

Lean statement: `D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For length at least nine, the coordinate-kernel bounds give radical site ranks at most one and support size at most ten. At length eight, a positive radical kernel on each pair bounds the joint rank by three. The length-eight shortening theorem therefore rules out every surjective radical site. The support size is at most eight in this case.

Restrict both spaces to the radical's occupied sites and relabel those sites. The projection is injective on the code, preserves its pairing with the radical, and can only decrease each nonradical word's zero count. Each occupied radical image has dimension one. The rank-one bridge excludes the resulting spaces.

**Theorem 1.3 (Reduction of exact attainment to the length-seven rank-two case).**

Lean statement: `D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.refute_attainment_of_length_seven_rank_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.refute_attainment_of_length_seven_rank_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact attainment requires weight at least n − 3 outside the radical and a nonradical word of weight exactly n − 3. The lower bound implies the three-zero condition. The radical needs at least seven occupied sites, and the general rank-one exclusion also rules out length seven when no radical site is surjective. An exclusion at length seven with a surjective radical site would therefore refute exact attainment.

## References

- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.claim`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.refute_attainment_of_length_seven_rank_two`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.result`
- Dependency: [D5/S3/Quantum/Codes/BinaryEAAttainment](BinaryEAAttainment.md)
- Dependency: [D5/S3/Quantum/Codes/BinaryEARankOneBridge](BinaryEARankOneBridge.md)
- Dependency: [D5/S3/Quantum/Codes/BinaryEAShortening](BinaryEAShortening.md)
