# From a native JointChoice to every natural prefix

## Abstract

Reconstructing one physical word and its inserted ear

**Lemma 1.1 (Physical reconstruction from natural masks).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Physical.actualSource_of_nativeChoice`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Physical.actualSource_of_nativeChoice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under a>b>d>c>=2 and one JointChoice, decode masks v,h,s-1,r-1 into original occurrence labels. The selected positive banks are (U minus Uv) union Wh union (X minus Xm), Xm minus Xu, and Uv union V union Xu; the fourth bank is W minus Wh. Bit inclusion proves Xu is contained in Xm. The proof preserves all c-1 V-positive occurrences, separate equal-valued labels and exact geometric masses.

**Lemma 1.2 (Exact selected-bank masses).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Physical.selected_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Physical.selected_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mass identities use the literal oldValue and newValue functions and the existing chamberLabels geometric sums. Natural capacity bounds justify each subtraction before conversion to integer algebra. The banks are followed by terminals X,V,U,W. The cut follows the first bank and X terminal, and marked_word identifies the enlarged word with the literal earWord at that same cut. The twelve gates bound the old and enlarged seams; four_strip and inStrip_prefix then cover empty, complete, overlong and all intermediate natural takes. Both row totals are exactly zero, with the fresh label contributing A.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Physical.actualSource_of_nativeChoice`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Physical.selected_mass`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source](Source.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Masks](../MaxPlusTwo/Chambers/Masks.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift](../../ThreeNegativeEqualOuterJointLift.md)
