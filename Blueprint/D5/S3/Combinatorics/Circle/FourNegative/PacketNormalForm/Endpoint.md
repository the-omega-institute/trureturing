# Four independent gaps, with no uniform allocation assumption

## Abstract

Exact four-packet reduction of the physical joint-order problem

**Definition 1.1 (Unordered physical certificate).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint.Certificate`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint.Certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For independent a,b,c,d>=2, k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c), Certificate contains just the four physical negative labels in any order, four finite sets partitioning the positive physical labels, one of four ear slots, and four old plus four new seam/peak pairs. A multiset identity partitions the complete actual label range; it preserves occurrence multiplicity even when numerical source values coincide. There is no OriginalOrder, all-prefix legality, J witness or favorable schedule among its assumptions.

**Theorem 1.2 (Necessity and sufficiency).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint.actual_four_packet_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint.actual_four_packet_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every independent a,b,c,d>=2, the existence of one physical sigma and j<=k satisfying OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) is equivalent to Nonempty(Certificate(a,b,c,d)). This is a reduction of unrestricted physical J; it does not assert that a certificate exists uniformly.

Write x=2^a,y=2^b,z=2^c,t=2^d,N=xyzt-1,W=2N+1. The original source_table is reused in its owner at d>=2. Old bases are F=[A,1+t+tx+txy,1+z+zt+ztx,1+y+yz+yzt] on chains of lengths [d,c,b,a]. Charges are eta=[0,1,1+z,1+y+yz], and new bases are 2F-eta. The new fourth successor is A, the fresh ear, rather than the enlarged first base. The exact centered chains have the same negative physical labels d-1,d+c-1,d+c+b-1,k-1. Every other old label is strictly positive in both rows; the old total is zero and the new old-label total is -A. Label k has new value A and is distinct from old zero.

Necessity fixes the original sigma. A valid old zero-sum word cannot end positive; hence the four negative labels split it into exactly four positive packets with no tail. The ear cannot be at the end because the preceding new height would be -A. It slides right over the remaining positive part of its current packet to the next negative. Both local paths have identical endpoints and nonnegative increments; every internal height remains in the legal strip. Sigma stays unchanged. The resulting four physical packets are then replaced by their finite sets, preserving both masses and every occurrence.

For a positive packet, mask m[c,r] is the geometric sum of 2^i over the actual retained positions i of chain c. The exact source formulas give p[r]=sum F[c]m[c,r] and new packet mass sum (2F[c]-eta[c])m[c,r]. The certificate adds A to the new mass in the selected ear packet. Starting from zero, each seam is the preceding seam plus packet mass plus the actual negative increment; each peak is the seam minus that negative increment. The only inequalities are seam>=0 and peak<=N/2 in the old row, and seam>=0 and peak<=N in the new row.

Sufficiency orders each finite positive packet in any internal physical order and follows its designated negative label. Since every packet step is positive in both coordinates, the two endpoint bounds imply all internal prefix bounds. Insert the literal fresh label immediately before the chosen negative. The physical partition yields one permutation of Fin(k), the ear bridge yields one numerical cut j, and the exact source totals give both zero sums. Natural take-prefixes include the empty and overlong cases. Empty packets, d=2, all equal gaps, nonprimitive seeds and repeated numerical source values are retained. No symmetry between unequal negative weights is assumed.

Uniform existence of the required physical masks remains OPEN, as do unrestricted physical J and Circle C3.1. The equivalence does not close that allocation gap.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint.Certificate`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint.actual_four_packet_iff`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Equivalence](Equivalence.md)
