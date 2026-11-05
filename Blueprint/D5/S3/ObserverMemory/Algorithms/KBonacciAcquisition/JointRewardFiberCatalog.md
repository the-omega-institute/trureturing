# Complete Catalog rewards and rigidity

## Abstract

Complete stopped rewards can prevent removal of A despite cellwise numerical dominance.

**Definition 1.1 (Boolean word carrier).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.Word`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural L, Word L is the entire Boolean cube Fin L to Bool. No competitor word is omitted.

**Definition 1.2 (One actual atom).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.point`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L, words a and b in Word L, and real t, point a t b is t when b equals a and zero otherwise.

**Definition 1.3 (Original stopped cell reward).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.reading`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.reading` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, real measure mu on Word L, original Schedule L and cell c in Fin 3, reading is the sum of mu over all words whose original StoppedCoefficientRealization.cell equals c. Empty and singleton schedules are included. Empty cells contribute zero.

**Definition 1.4 (Equality before maximization).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.SameReadings`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.SameReadings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and real measures mu and nu on Word L, SameReadings means equality of reading for every original stopped schedule and every cell. It asserts equality of individual rewards before any maxima, rather than equality of supports or costs.

**Definition 1.5 (Original first-zero class).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.FirstZero`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.FirstZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, Boolean word b and address i in Fin L, FirstZero b i means b i is false and b h is true for every h strictly before i. The address i corresponds to original numerical output label i+1.

**Definition 1.6 (Independent full score coefficients).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.FullScore`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.FullScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, FullScore L contains independent real coefficient functions A, C and P on all Boolean words and a real terminal coefficient T. All coefficients are nonnegative. A, C and P at the all-true terminal word are normalized to zero; T is its independent coefficient. Thus every original nonterminal A/C/P coordinate remains available to competitors.

**Definition 1.7 (Zero-label measure).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.baseline`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.baseline` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y and word b, baseline y b is A(b)+P(b), plus T precisely at the all-true word. This is the actual zero-label reward measure.

**Definition 1.8 (Every numerical label).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.numerical`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.numerical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y, address i and word b, numerical y i b is C(b)+P(b) when FirstZero b i holds, and zero otherwise. All L numerical labels are retained, in addition to the baseline label zero.

**Definition 1.9 (Total independent coefficient mass).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.coefficientMass`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.coefficientMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, coefficientMass y is the sum of A(b)+C(b)+P(b) over the entire cube, plus T. Shared P is counted exactly once.

**Definition 1.10 (Signed first-zero totals).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.beta`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y and address i, beta y i is the sum of C(b)-A(b) over words in FirstZero class i.

**Definition 1.11 (The complete reward fiber).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.SameFiber`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.SameFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full scores y and z, SameFiber y z means equality of their entire beta functions, equality of all baseline stopped-cell readings, and equality of all numerical stopped-cell readings at every address. No cell-to-moment equivalence is assumed.

**Definition 1.12 (The selected suffix 000 word).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.baseWord`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.baseWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and n,j,k,l in Fin L, baseWord sets precisely those four addresses to false and all other addresses to true. Under n<j<k<l this has first zero n and selected suffix bits 000. Original source indices are obtained by adding one to these zero-based addresses.

**Definition 1.13 (Three selected singleton words).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.singletonWord`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.singletonWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and n,j,k,l,a in Fin L, singletonWord changes baseWord only at a, setting that bit to true. For a=j,k,l these are exactly the source suffix words 100,010,001.

**Definition 1.14 (The numerical source measure).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.threePoints`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.threePoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, addresses n,j,k,l, real t and word b, threePoints is the sum of point masses t at the three singletonWord words selected by j,k,l. Coincident atoms add, although the theorem requires strictly increasing selected addresses.

**Definition 1.15 (The actual four-word source score).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.witnessScore`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.witnessScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, n<j<k<l in Fin L, real t at least zero, witnessScore has A=t at baseWord, C=t at the three singletonWord words, P identically zero and T=0. Its nonnegativity and terminal normalization are proved. The original late-class condition is n.val at least 2; the rigidity theorem also holds without that restriction.

**Theorem 1.16 (Arbitrary full competitors have zero shared mass).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.proposition21310_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.proposition21310_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural L, n<j<k<l in Fin L, positive real t, and arbitrary FullScore y in the complete SameFiber of witnessScore, P is zero at every Boolean word, T is zero, A at baseWord equals t, coefficientMass is 4t, and A is not identically zero. Every original stopped schedule-cell numerical reward of witnessScore at label n+1 dominates its baseline reward; this includes the empty and singleton schedules and every empty cell. At least one of the three singleton words agrees with the base word at both possible queried addresses. All competitor words, first-zero classes and labels remain available, and their masses are arbitrary nonnegative reals. In original one-based notation this applies to every 3<=n<j<k<l<=L by subtracting one from the four addresses.

The proof extracts only the empty-cell total, singleton success rewards and stopped pair-11 rewards from the actual supplier cells. Singleton zero readings force the entire baseline measure onto baseWord. The nonnegative quadratic 1-zj-zk-zl+zj*zk+zj*zl+zk*zl has zero integral under the numerical measure but value one at baseWord. It therefore forbids numerical mass there. Nonnegative P is shared by both measures at the same actual word, so P vanishes everywhere. A finite first-zero partition accounts for all numerical labels and gives the exact coefficient mass without assuming a general cell-to-moment equivalence.

The obstruction concerns removal of A within the specified complete reward fiber. These are proof weights on one finite cube, not acquisition probabilities. It implies no unrestricted-repair or E_N nonmembership claim and asserts no literature novelty.

**Definition 1.17 (Complete N cells).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.fullCell`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.fullCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, original Schedule L and raw Boolean word, fullCell gives the four cells 00,01,10,11 in that order for a distinct ordered pair. Empty schedules use cell zero. Singletons use cells zero and one. Other short-schedule cells are empty.

**Definition 1.18 (Both original partitions).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalogCell`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalogCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, stop, schedule and word, catalogCell uses the existing stopped cell when stop is true and fullCell when stop is false. Stopped indices zero, one and two embed in Fin 4, whose final cell is empty. Thus the two values of stop denote the complete O and N catalogs respectively.

**Definition 1.19 (Every complete cell reward).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalogReading`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalogReading` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, real measure on the full cube, stop, original schedule and Fin 4 cell, catalogReading sums that same measure over precisely the words in the selected original cell. Zero mass and empty cells are included.

**Definition 1.20 (All original numerical and zero labels).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.labelReading`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.labelReading` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y, stop, schedule, cell and output r in Fin (L+1), labelReading is catalogReading of the baseline when r=0 and of numerical y i when r=i+1. This is the complete reward g of Definition 213.1 with the original first-zero labels.

**Definition 1.21 (One whole table).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.scheduleReward`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.scheduleReward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y, stop, original schedule and arbitrary map from Fin 4 to Fin (L+1), scheduleReward sums labelReading using that table's output in each cell. Every original output label is allowed independently in every cell.

**Definition 1.22 (Complete support before anchor subtraction).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.completeSupport`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.completeSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, stop and full score y, completeSupport is the supremum of fullReward over every whole output function in the original Catalog stop L. The exact Catalog range and cell-sum identities equate it to the supremum of scheduleReward over every empty, singleton and distinct ordered pair schedule with unrestricted cell labels. This finite range is exactly the maximization over all cell maxima and schedules in Definition 213.1. The empty cells added for short and stopped tables contribute zero.

**Definition 1.23 (The original head-pair anchor).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.anchor`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.anchor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, anchor is the reward of referenceHead. When L is at least two this is the original reference head pair R=(1,2;1,2,0), whose full-cell completion is (1,1,2,0). When L is smaller, referenceHead uses the available first addresses, including the empty head at L=0. The proved formula sums A over first-zero classes whose zero-based address is at least two, C over the two earlier classes, every P once and T once. Original index n is the zero-based address plus one, so the late condition is the original inequality 3<=n.

**Definition 1.24 (Complete excess over the anchor).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.completeCost`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.completeCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, stop and full score, completeCost is completeSupport minus anchor. True stop denotes Delta O and false stop denotes Delta N.

**Definition 1.25 (Whole output functions).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.evaluate`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.evaluate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each stop mode, schedule and unrestricted assignment of all original output labels to all four cells, evaluate is the function on every Boolean word obtained by reading its catalogCell and that cell label.

**Theorem 1.26 (The exact original Catalog range).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalog_range`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalog_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, both stop modes and every whole output function f on the complete Boolean cube, InCatalog stop L f holds if and only if f is evaluate stop s a for some local schedule s and unrestricted cell labels a. The nonstopped proof includes empty and singleton schedules, repeated requests and reversed pairs: repeats need only one bit, while reversal permutes the four cell labels. The stopped direction reuses StoppedCoefficientRealization.represented, retaining its increasing order and first-false asymmetry. This is equality of output-function ranges; representations need not be unique and paid request histories need not agree.

**Definition 1.27 (The original FullScore functional).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.fullReward`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.fullReward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every FullScore y and whole output function f, fullReward sums baseline y b when f b is zero and numerical y i b when f b is i+1, over every Boolean word b. Thus output zero receives A+P and terminal T, and output i+1 receives C+P exactly on FirstZero b i. Earlier and unqueried labels, all zero weights and the terminal remain in scope.

**Theorem 1.28 (Cell sums equal whole-function rewards).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.schedule_reward_eq`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.schedule_reward_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, stop, full score, local schedule and cell labels, scheduleReward equals fullReward evaluated at the whole output function evaluate. The finite sums are rearranged over the complete cube, including every empty cell.

**Theorem 1.29 (Original and local maximizations coincide).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.complete_support_eq_local`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.complete_support_eq_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, stop and FullScore y, the supremum of fullReward over the original Catalog equals the supremum of scheduleReward over all local schedules and cell label assignments. Both inclusions use catalog_range and schedule_reward_eq.

**Definition 1.30 (Original reference head).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.referenceHead`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.referenceHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

referenceHead returns the original numerical label i+1 when the first zero occurs at one of the first two available addresses, and zero otherwise. Its choice is unique because FirstZero classes are disjoint. No further address can affect this output.

**Theorem 1.31 (Reference reward equals the anchor formula).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.anchor_eq_formula`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.anchor_eq_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L and FullScore y, the reward of referenceHead equals the sum of A in first-zero classes at addresses at least two, C in the earlier two classes, all P once and terminal T once. A finite first-zero partition proves this identity, including the all-true word and dimensions with fewer than two addresses.

**Theorem 1.32 (Local tables are native Catalog functions).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.evaluated_in_catalog`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.evaluated_in_catalog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, stop, schedule and unrestricted cell label assignment, the whole evaluated output function belongs to the original InCatalog. In stopped mode it is the existing StoppedCoefficientRealization.table with an unused fourth cell; the nonstopped direction uses the original low-address view and its complete replies.

**Theorem 1.33 (Native output fibers are unions of local cells).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalog_fiber_sum`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalog_fiber_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, stop, arbitrary real measure mu on all words, schedule, cell labels and original output r, the mass of the whole output fiber f=r equals the sum of precisely those local cell masses assigned r. This identity is before maximization and requires no sign or support restriction.

**Theorem 1.34 (Complete stopped observations in native form).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.same_readings_iff_catalog`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.same_readings_iff_catalog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L and arbitrary real measures mu and nu on the whole cube, SameReadings is equivalent to equality of the mass of every output fiber of every function in the original Catalog true L. Each output fiber is a union of local cells. Conversely, each local cell is selected by a native table assigning it zero and assigning a distinct numerical output to the other cells; dimension zero is handled separately. The equivalence retains all short schedules and empty cells.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.FirstZero`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.FullScore`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.SameFiber`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.SameReadings`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.Word`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.anchor`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.anchor_eq_formula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.baseWord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.baseline`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.beta`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalogCell`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalogReading`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalog_fiber_sum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.catalog_range`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.coefficientMass`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.completeCost`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.completeSupport`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.complete_support_eq_local`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.evaluate`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.evaluated_in_catalog`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.fullCell`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.fullReward`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.labelReading`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.numerical`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.point`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.proposition21310_rigidity`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.reading`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.referenceHead`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.same_readings_iff_catalog`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.scheduleReward`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.schedule_reward_eq`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.singletonWord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.threePoints`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog.witnessScore`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization](StoppedCoefficientRealization.md)
