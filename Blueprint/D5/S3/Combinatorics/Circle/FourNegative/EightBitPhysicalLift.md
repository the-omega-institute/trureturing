# Insertion-only physical lift with exact target rectangle

## Abstract

Corrected eight-bit physical insertion and the (2,2,2,d) family

**Definition 1.1 (Insertion label maps).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.liftOldLabel`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.liftOldLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The eight inserted labels occupy target labels 0 through 7. Every original label, including the fresh occurrence, is shifted by eight; targetN and targetH are the corrected physical bounds.

**Definition 1.2 (Fresh label map).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.liftFreshLabel`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.liftFreshLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original fresh occurrence is shifted by eight with the other original labels.

**Definition 1.3 (New label map).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.liftNewLabel`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.liftNewLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The eight inserted labels are represented by Fin 8 and embed into the target range.

**Definition 1.4 (Mask update).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionMaskUpTo`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionMaskUpTo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mask after an inserted bit is the canonical residue of the updated old bit sum.

**Definition 1.5 (First endpoint).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonicalFirst`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonicalFirst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first endpoint is the exact affine physical lift expression.

**Definition 1.6 (Second endpoint).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonicalSecond`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonicalSecond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second endpoint includes the fresh correction and the inserted doubled labels.

**Definition 1.7 (Canonical inserted mask).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionMask`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inserted physical mask is the old bit sum reduced modulo 256.

**Definition 1.8 (Corrected target bounds).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.targetN`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.targetN` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first physical capacity is Hprime=256H+255. The second is Nprime=256N+255.

**Definition 1.9 (Corrected target half bound).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.targetH`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.targetH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The target half bound is 256H+255.

**Definition 1.10 (Literal pair schedule).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.physicalLiftWord`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.physicalLiftWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word is built by flat-mapping the original word and choosing one of the two orders for each old/new pair.

**Definition 1.11 (Deletion filter).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionDeletion`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionDeletion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filtering target labels at least eight and subtracting eight recovers original labels.

**Theorem 1.12 (Deletion recovers every original occurrence).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionDeletion_physicalLiftWord`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionDeletion_physicalLiftWord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target has eight new physical labels 0 through 7. Every old label i is mapped to i+8, including the fresh occurrence, and the local word emits each new label exactly once adjacent to its corresponding original label. Filtering away labels below 8 recovers the complete original word in its original relative order.

The canonical first and second endpoint expressions are 256F-255C+85u and 256Y-255C-21675b+170u, with u=T mod 256. The corrected physical bounds are N'=256N+255 and H'=256H+255. The endpoint lift identity expresses the target state as the old state plus r(21760,43520) whenever u+3F-3C=256r.

The module also records the literal four-gap family gaps (2,2,2,d), its period and seed, the uniform physical sparse-necklace contract, eight checked seeds for d=2,...,9, and the unconditional family witness for every d>=2. The family proof repeatedly applies the insertion-only lift in steps of eight to the eight kernel-checked seeds.

**Theorem 1.13 (Canonical endpoint arithmetic).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonical_endpoint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonical_endpoint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This algebraic lemma is conditional on its displayed residue, nonnegativity and room hypotheses. The complete-prefix theorem separately derives these bounds from a legal full physical word, and handles k=8 by F in {0,85} and Fprime=257F.

**Theorem 1.14 (Target modulus identities).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.target_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.target_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target modulus and half-modulus identities reduce to 256N+255 and 256H+255.

**Theorem 1.15 (Mask range).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertion_mask_range`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertion_mask_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every canonical inserted mask lies between 0 and 255.

**Theorem 1.16 (Endpoint relation).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonical_endpoint_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonical_endpoint_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two endpoint coordinates retain the joint relation Y=2F-C+85b.

**Theorem 1.17 (The four-gap period).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps_period`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal gap tuple (2,2,2,d) has period d+6 and seed 85.

**Definition 1.18 (The four gap tuple).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tuple is literally (2,2,2,d).

**Theorem 1.19 (The family seed).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps_seed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps_seed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tuple's physical necklace seed is 85.

**Theorem 1.20 (Uniform physical rounding contract).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.physical_rounding_family_contract`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.physical_rounding_family_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The already verified uniform sparse-necklace theorem applies to every legal (2,2,2,d) tuple.

**Theorem 1.21 (Every (2,2,2,d) family member has a physical joint word).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps_family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each d>=2 there is a sigma on Fin(d+6) with OriginalOrder(d+6,85,sigma), together with a literal ear cut producing OriginalOrder(d+7,170,earWord(d+6,sigma,cut)). The proof uses all eight finite seeds d=2 through 9 and induction by eight with insertion_only_eight_bit_lift. The separately retained eventual theorem is not used on this proof path.

**Theorem 1.22 (Canonical bounds from the complete physical inventory).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftPrefix.canonical_complete_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftPrefix.canonical_complete_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every legal full physical word and every natural prefix, the actual nonnegative charge sum is at most 85 and the sum of encountered low binary weights is at most 255. High binary weights are divisible by 256. The native digit identities give the integral parameter r and its range for k>=9. For k=8, the old first height is 0 or 85, giving firstState=257F and secondState=Y+512F. Thus both canonical endpoints are inside the corrected target rectangle without additional residue, charge, room or feasibility hypotheses.

**Theorem 1.23 (Native quotient parity controls every paired row).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftLocal.low_row_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftLocal.low_row_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k>=9 and every paired index i<8, division of 85 by the native dyadic denominator has an odd positive remainder. Even quotient gives a mapped row positive in both coordinates. Odd quotient gives a negative first row whose span with the inserted row is at most Hprime-171. This uniform arithmetic proof has no bound on k and performs no search over physical words or masks.

**Theorem 1.24 (Every legal full word admits the shared physical lift).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftSchedule.physical_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftSchedule.physical_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k>=8 and every JointWord k w, one orientation is chosen from w's actual prefix before each paired label. The common charge corridor is equivalent to both physical bounds. A positive pair is monotone; for a negative pair the corridor span bound guarantees old-first when new-first fails. At k=8 the sharper canonical height 21845 makes new-first fit. Induction on take-prefixes appends each legal literal block and proves every intermediate prefix. The target is a once-only permutation, both totals are zero, and deletion recovers w exactly, including fresh and all original relative order.

**Theorem 1.25 (Insertion-only lift in OriginalOrder and earWord).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftBridge.insertion_only_eight_bit_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftBridge.insertion_only_eight_bit_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every legal old order and its legal literal fresh insertion in dimension k>=8 produce an old order in dimension k+8 and a fresh cut in dimension k+9. Filtering target labels below eight and subtracting eight from the retained labels recovers the entire original earWord. The bridge removes only the unique fresh label to recover the old order, transfers every projected prefix, and finds the new cut at fresh's actual position. The result is the universal +8 insertion theorem used by the eight-seed family induction. Its scope is the fixed gaps (2,2,2,d), not arbitrary four-gap joint orders.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonicalFirst`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonicalSecond`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonical_endpoint_formula`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.canonical_endpoint_lift`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionDeletion`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionDeletion_physicalLiftWord`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionMask`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertionMaskUpTo`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.insertion_mask_range`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.liftFreshLabel`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.liftNewLabel`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.liftOldLabel`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.physicalLiftWord`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.targetH`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.targetN`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic.target_bounds`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftBridge.insertion_only_eight_bit_lift`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftLocal.low_row_parity`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftPrefix.canonical_complete_prefix`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftSchedule.physical_joint_lift`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps_family`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps_period`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.fourGaps_seed`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift.physical_rounding_family_contract`
