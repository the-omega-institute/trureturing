# Joint reward-fiber obstruction

## Abstract

Complete stopped rewards can prevent removal of A despite cellwise numerical dominance.

**Definition 1.1 (Boolean word carrier).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.Word`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural L, Word L is the entire Boolean cube Fin L to Bool. No competitor word is omitted.

**Definition 1.2 (One actual atom).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.point`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L, words a and b in Word L, and real t, point a t b is t when b equals a and zero otherwise.

**Definition 1.3 (Original stopped cell reward).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.reading`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.reading` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, real measure mu on Word L, original Schedule L and cell c in Fin 3, reading is the sum of mu over all words whose original StoppedCoefficientRealization.cell equals c. Empty and singleton schedules are included. Empty cells contribute zero.

**Definition 1.4 (Equality before maximization).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.SameReadings`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.SameReadings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and real measures mu and nu on Word L, SameReadings means equality of reading for every original stopped schedule and every cell. It asserts equality of individual rewards before any maxima, rather than equality of supports or costs.

**Definition 1.5 (Original first-zero class).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.FirstZero`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.FirstZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, Boolean word b and address i in Fin L, FirstZero b i means b i is false and b h is true for every h strictly before i. The address i corresponds to original numerical output label i+1.

**Definition 1.6 (Independent full score coefficients).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.FullScore`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.FullScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, FullScore L contains independent real coefficient functions A, C and P on all Boolean words and a real terminal coefficient T. All coefficients are nonnegative. A, C and P at the all-true terminal word are normalized to zero; T is its independent coefficient. Thus every original nonterminal A/C/P coordinate remains available to competitors.

**Definition 1.7 (Zero-label measure).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.baseline`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.baseline` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y and word b, baseline y b is A(b)+P(b), plus T precisely at the all-true word. This is the actual zero-label reward measure.

**Definition 1.8 (Every numerical label).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.numerical`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.numerical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y, address i and word b, numerical y i b is C(b)+P(b) when FirstZero b i holds, and zero otherwise. All L numerical labels are retained, in addition to the baseline label zero.

**Definition 1.9 (Total independent coefficient mass).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientMass`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, coefficientMass y is the sum of A(b)+C(b)+P(b) over the entire cube, plus T. Shared P is counted exactly once.

**Definition 1.10 (Signed first-zero totals).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.beta`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y and address i, beta y i is the sum of C(b)-A(b) over words in FirstZero class i.

**Definition 1.11 (The complete reward fiber).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.SameFiber`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.SameFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full scores y and z, SameFiber y z means equality of their entire beta functions, equality of all baseline stopped-cell readings, and equality of all numerical stopped-cell readings at every address. No cell-to-moment equivalence is assumed.

**Definition 1.12 (The selected suffix 000 word).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.baseWord`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.baseWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and n,j,k,l in Fin L, baseWord sets precisely those four addresses to false and all other addresses to true. Under n<j<k<l this has first zero n and selected suffix bits 000. Original source indices are obtained by adding one to these zero-based addresses.

**Definition 1.13 (Three selected singleton words).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.singletonWord`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.singletonWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and n,j,k,l,a in Fin L, singletonWord changes baseWord only at a, setting that bit to true. For a=j,k,l these are exactly the source suffix words 100,010,001.

**Definition 1.14 (The numerical source measure).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.threePoints`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.threePoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, addresses n,j,k,l, real t and word b, threePoints is the sum of point masses t at the three singletonWord words selected by j,k,l. Coincident atoms add, although the theorem requires strictly increasing selected addresses.

**Definition 1.15 (The actual four-word source score).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.witnessScore`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.witnessScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, n<j<k<l in Fin L, real t at least zero, witnessScore has A=t at baseWord, C=t at the three singletonWord words, P identically zero and T=0. Its nonnegativity and terminal normalization are proved. The original late-class condition is n.val at least 2; the rigidity theorem also holds without that restriction.

**Theorem 1.16 (Arbitrary full competitors have zero shared mass).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural L, n<j<k<l in Fin L, positive real t, and arbitrary FullScore y in the complete SameFiber of witnessScore, P is zero at every Boolean word, T is zero, A at baseWord equals t, coefficientMass is 4t, and A is not identically zero. Every original stopped schedule-cell numerical reward of witnessScore at label n+1 dominates its baseline reward; this includes the empty and singleton schedules and every empty cell. At least one of the three singleton words agrees with the base word at both possible queried addresses. All competitor words, first-zero classes and labels remain available, and their masses are arbitrary nonnegative reals. In original one-based notation this applies to every 3<=n<j<k<l<=L by subtracting one from the four addresses.

The proof extracts only the empty-cell total, singleton success rewards and stopped pair-11 rewards from the actual supplier cells. Singleton zero readings force the entire baseline measure onto baseWord. The nonnegative quadratic 1-zj-zk-zl+zj*zk+zj*zl+zk*zl has zero integral under the numerical measure but value one at baseWord. It therefore forbids numerical mass there. Nonnegative P is shared by both measures at the same actual word, so P vanishes everywhere. A finite first-zero partition accounts for all numerical labels and gives the exact coefficient mass without assuming a general cell-to-moment equivalence.

The live new content is universal shared-support rigidity, rather than scaling a finite catalog. The witness constructor and finite-sum identities serve that argument. This source does not establish the general compactness and moment-cone equivalence of Theorem 213.8, the cone optimization J(y), the floor formula, the complete N/O cost calculations, or unrestricted-repair and E_N nonmembership claims. The proposition's remaining clauses stay open; this module supplies the universal coefficient obstruction only. These are proof weights on one finite cube, not acquisition probabilities. No literature novelty classification is asserted.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.FirstZero`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.FullScore`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.SameFiber`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.SameReadings`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.Word`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.baseWord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.baseline`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.beta`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientMass`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.numerical`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.point`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_rigidity`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.reading`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.singletonWord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.threePoints`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.witnessScore`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization](StoppedCoefficientRealization.md)
