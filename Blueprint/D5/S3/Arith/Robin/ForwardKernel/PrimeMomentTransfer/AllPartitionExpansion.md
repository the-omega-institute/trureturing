# All partition expansion

## Abstract

An index-independent enumeration of arbitrary-order collision partitions.

**Theorem 1.1 (Every partition has a finite-label tuple).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.tupleKernelPatterns_fin_universal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.tupleKernelPatterns_fin_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and every setoid sigma on Fin k, sigma belongs to tupleKernelPatterns(k,Fin k). The quotient of sigma has at most k elements. Composing its injection into Fin k with the quotient map gives a tuple whose kernel is exactly sigma. This includes k=0.

**Theorem 1.2 (Summing the zero-degree configurations).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.sum_pairing_partition_configurations`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.sum_pairing_partition_configurations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural k and real-valued function G on partial pairings of Fin k, sum G over all partitions sigma and retained subsets S whose retained blocks have size one and whose unretained blocks have size two, evaluating G at their unretained two-element blocks. This sum equals the sum of G over all partial pairings, with each counted exactly once. The bijection between these configurations and partial pairings introduces no ordering or factorial factor.

**Theorem 1.3 (The same partition set for every index type).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.quadratic_moment_eq_all_partition_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.quadratic_moment_eq_all_partition_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the index type be finite, A a commutative real algebra, ell:A->R real linear, and Y(d)^2=a*Y(d)+b*1 for all d. For any coefficient family f indexed by Fin k, quadraticFamilyMoment equals the sum over sigma in tupleKernelPatterns(k,Fin k) and all retained block sets S of product_(B in S) u(size(B)), times product_(B outside S) v(size(B)), times kernelDistinctMoment(ell,Y,f,sigma,S). Here u and v are quadraticPowerCoeffs and size(B)=mult(Quotient.mk sigma,B). Every partition absent from the index-type tuple kernels has an empty exact-kernel sum and contributes zero. No centering, normalization, positivity or independence is needed.

**Theorem 1.4 (The coefficient of a partial pairing).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.pairingPartition_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.pairingPartition_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any PairingPartitionData D and real a,b, the product of u(size(B)) over its retained blocks times the product of v(size(B)) over its unretained blocks equals b^(card(pairingPartitionPairs(D))). Every retained size is one, giving u(1)=1; every unretained size is two, giving v(2)=b. The bijection with partial pairings preserves the number of unretained blocks.

**Theorem 1.5 (A uniform configuration count).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.all_partition_configuration_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.all_partition_configuration_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, the sum over sigma in tupleKernelPatterns(k,Fin k) of the number of finite subsets of Quotient sigma is at most k^k*2^k. The partition set is an image of the k^k functions from Fin k to itself, and each quotient has at most k elements, giving at most 2^k retained subsets. At k=0 both factors and the configuration count equal one.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.all_partition_configuration_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.pairingPartition_coefficient`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.quadratic_moment_eq_all_partition_expansion`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.sum_pairing_partition_configurations`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AllPartitionExpansion.tupleKernelPatterns_fin_universal`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence](PairingPartitionCorrespondence.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion](PartitionCollisionExpansion.md)
