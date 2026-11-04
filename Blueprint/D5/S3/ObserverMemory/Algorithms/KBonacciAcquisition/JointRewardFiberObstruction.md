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

The obstruction concerns removal of A within the specified complete reward fiber. These are proof weights on one finite cube, not acquisition probabilities. It implies no unrestricted-repair or E_N nonmembership claim and asserts no literature novelty.

**Definition 1.17 (Complete N cells).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.fullCell`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.fullCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, original Schedule L and raw Boolean word, fullCell gives the four cells 00,01,10,11 in that order for a distinct ordered pair. Empty schedules use cell zero. Singletons use cells zero and one. Other short-schedule cells are empty.

**Definition 1.18 (Both original partitions).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.catalogCell`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.catalogCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, stop, schedule and word, catalogCell uses the existing stopped cell when stop is true and fullCell when stop is false. Stopped indices zero, one and two embed in Fin 4, whose final cell is empty. Thus the two values of stop denote the complete O and N catalogs respectively.

**Definition 1.19 (Every complete cell reward).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.catalogReading`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.catalogReading` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, real measure on the full cube, stop, original schedule and Fin 4 cell, catalogReading sums that same measure over precisely the words in the selected original cell. Zero mass and empty cells are included.

**Definition 1.20 (All original numerical and zero labels).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.labelReading`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.labelReading` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y, stop, schedule, cell and output r in Fin (L+1), labelReading is catalogReading of the baseline when r=0 and of numerical y i when r=i+1. This is the complete reward g of Definition 213.1 with the original first-zero labels.

**Definition 1.21 (One whole table).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.scheduleReward`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.scheduleReward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y, stop, original schedule and arbitrary map from Fin 4 to Fin (L+1), scheduleReward sums labelReading using that table's output in each cell. Every original output label is allowed independently in every cell.

**Definition 1.22 (Complete support before anchor subtraction).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.completeSupport`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.completeSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, stop and full score y, completeSupport is the supremum of scheduleReward over every original empty, singleton and distinct ordered pair schedule and every cell-label table. This finite range is exactly the maximization over all cell maxima and schedules in Definition 213.1. The empty cells added for short and stopped tables contribute zero.

**Definition 1.23 (The original head-pair anchor).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.anchor`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.anchor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, anchor sums A over all first-zero classes whose zero-based address is at least two, C over the two earlier classes, every P once and T once. Original index n is the zero-based address plus one, so the late condition is the original inequality 3<=n.

**Definition 1.24 (Complete excess over the anchor).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.completeCost`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.completeCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, stop and full score, completeCost is completeSupport minus anchor. True stop denotes Delta O and false stop denotes Delta N.

**Definition 1.25 (Original quadratic coordinates).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.feature`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.feature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, word and coordinate in Unit plus singleton addresses plus ordered distinct pairs, feature is the constant one, the selected bit, or the product of the selected two bits. The coordinate carrier uses Schedule L as an index set; it does not replace the words or their first-zero classes.

**Definition 1.26 (Actual full-cube moments).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.moments`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.moments` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and arbitrary real measure mu on the raw Boolean cube, moments mu sums mu times feature in each constant, singleton and ordered pair coordinate.

**Definition 1.27 (Actual first-zero moment cone).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.MomentCone`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.MomentCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, first-zero address i and complete quadratic vector v, MomentCone i v means that one actual nonnegative real measure on the entire cube represents v and vanishes outside the original class FirstZero i. No relaxation to independent marginal data is made.

**Definition 1.28 (Baseline mass in each first-zero class).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.classBaselineMass`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.classBaselineMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y and address i, classBaselineMass sums A+P over precisely the original class FirstZero i. Terminal T is separate.

**Definition 1.29 (The coupled common-P constraints).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.CoupledFeasible`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.CoupledFeasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y and families x,p of complete quadratic vectors indexed by every first-zero class, CoupledFeasible requires p, x-p and moments(numerical y i)-p to lie in the corresponding actual MomentCone; x's constant coordinate equals classBaselineMass; and the sum of all x vectors plus T times the terminal feature equals moments(baseline y). The same p is used in both differences, and the last equation is one aggregate equation on the common cube.

**Definition 1.30 (All feasible common masses).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.commonMassSet`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.commonMassSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, commonMassSet contains exactly the sums of constant coordinates of p over all x,p satisfying CoupledFeasible. It includes all actual feasible variables and retains a single shared P vector for each class.

**Definition 1.31 (The coupled optimum J).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.jointMaximum`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.jointMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, jointMaximum is the supremum of commonMassSet. The theorem below proves that this supremum is an attained greatest element equal to zero for the four-word family.

**Definition 1.32 (The original coefficient floor).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientFloor`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientFloor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, coefficientFloor is T plus the sum over every first-zero class of the maximum of its baseline mass and its numerical-label mass. It is K floor in Definition 213.7 and Theorem 213.8.

**Definition 1.33 (All actual fiber coefficient masses).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.fiberMassSet`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.fiberMassSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, fiberMassSet consists of coefficientMass z for all arbitrary nonnegative full scores z in SameFiber z y. All raw words, first-zero classes and original individual rewards remain constrained.

**Definition 1.34 (The fiber coefficient minimum).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientMinimum`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientMinimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, coefficientMinimum is the infimum of fiberMassSet. The theorem below supplies a least element and an actual attaining score for this family, without assuming Theorem 213.8.

**Theorem 1.35 (Complete N and O costs).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_costs`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_costs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, ordered zero-based addresses n<j<k<l, late address n.val>=2 and positive real t, let y be witnessScore. Its entire beta function is 2t at n and zero elsewhere, its original anchor is t, and both complete supports are 3t and both complete costs are 2t. For every original schedule, every N or O cell and every empty cell, numerical label n+1 dominates the zero-label reward. The proof bounds every label choice in every complete table and exhibits the constant numerical-label table attaining 3t; it uses no restriction on competitor supports.

**Theorem 1.36 (Attained joint and coefficient extrema).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_cone_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_cone_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, n<j<k<l and positive real t, let y be witnessScore. Zero is a greatest element of commonMassSet and jointMaximum is zero. For all actual feasible x,p, every vector p i is zero. The value 4t is a least element of fiberMassSet, coefficientMinimum is 4t, coefficientFloor is 3t and the floor is strictly smaller than the minimum. An explicit feasible choice takes x at class n to be the moments of the actual base point of mass t, all other x to be zero and the shared p to be zero in every class. The source score itself attains the coefficient minimum. The cone proof chooses one P measure, one A residual and one C residual for each class, assembles the aggregate baseline, and applies the same nonnegative quadratic support separation. Direct polynomial formulas recover actual stopped readings from the complete moment vector; no general attainment or independent-P reconstruction theorem is assumed.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.CoupledFeasible`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.FirstZero`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.FullScore`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.MomentCone`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.SameFiber`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.SameReadings`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.Word`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.anchor`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.baseWord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.baseline`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.beta`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.catalogCell`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.catalogReading`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.classBaselineMass`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientFloor`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientMass`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientMinimum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.commonMassSet`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.completeCost`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.completeSupport`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.feature`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.fiberMassSet`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.fullCell`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.jointMaximum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.labelReading`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.moments`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.numerical`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.point`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_cone_minimum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_costs`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_rigidity`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.reading`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.scheduleReward`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.singletonWord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.threePoints`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.witnessScore`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization](StoppedCoefficientRealization.md)
