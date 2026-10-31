# Necessary physical order for the unbounded four-gap lattice family

## Abstract

Necessary physical order for the unbounded four-gap lattice family

**Theorem 1.1 (Delta is the first or second negative).**

Lean statement: `D5/S3/Combinatorics/Circle/Lattice/FourNegativeLatticePrecedence.actualSource_four_gap_lattice_precedence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Lattice/FourNegativeLatticePrecedence.actualSource_four_gap_lattice_precedence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=1 set t=4n+2, k=2t+4, x=2^t, A=1+2^t+2^(t+2)+2^(2t+2), and N=2^k-1. Assume precisely an OriginalOrder at (k,A) and an OriginalOrder at (k+1,2A) obtained by one literal earWord insertion at j<=k. There is no assumed lattice or charge table at this endpoint. The physical labels alpha=1, beta=t+1, gamma=t+3, delta=k-1 remain separate even when their old values coincide.

The arithmetic gives A=4x^2+5x+1, N=16x^2-1, B=5(4x+1), and H=(N-B)/2. Since 2^(4n+2) is 4 modulo 5, putting r=(x+1)/5 gives A=rB, N=(4r-1)B and H=(2r-1)B. Every actual old centered value is in B times the integers, using digit_data's exact raw source identity. The old cap is (N-1)/2, and H is its largest accessible lattice height.

PeriodicShorteningArithmetic.digit_data supplies all actual charge nonnegativity and the literal castSucc new-source equation, while charge_sum supplies the full total A. The fresh source value is A by centered_full_period. The alpha and gamma values are both -H. Their charges are strictly positive, and delta's binary digit charge is (A+1)/2>B throughout this entire family. Therefore the same actual suffix at either alpha or gamma has budget N-2H=B, which cannot contain delta. Delta precedes both; the fresh ear also precedes both.

For the sign inventory, the numerical source has period t+2: 2^(t+2)A=A+N(x+1). In one such period only labels 1 and t+1 can be negative; the intervening values are 2^s B and the initial value is A. Applying the identity to the second period identifies exactly the possible negative labels alpha,beta,gamma,delta without identifying their physical occurrences or their paired charges. Consequently every negative before delta is beta, and the set of such physical labels is subsingleton. Since the order is a permutation, each physical label occurs once, so at most one negative occurs before delta.

This uniform n>=1 theorem excludes a universal constructor that keeps delta third or last, irrespective of positive masks or adaptive insertion. It imposes no order between delta and the ear and does not select between delta first and second. It does not rule out a different universal constructor with delta first or second. The remaining unrestricted constructive obligation is still to produce, for every four-gap parameter tuple, an old physical permutation and one literal insertion with all old and new prefix bounds and both full zero totals for arbitrary four independent gaps at least two. Physical J and full Circle C3.1 remain open; no literature novelty is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Lattice/FourNegativeLatticePrecedence.actualSource_four_gap_lattice_precedence`
- Dependency: [D5/S3/Combinatorics/Circle/Lattice/LatticeChargePrecedence](LatticeChargePrecedence.md)
