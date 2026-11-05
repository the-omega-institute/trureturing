# Joint reward-fiber obstruction

## Abstract

Complete stopped rewards can prevent removal of A despite cellwise numerical dominance.

**Definition 1.1 (Original quadratic coordinates).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.feature`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.feature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, word and coordinate in Unit plus singleton addresses plus ordered distinct pairs, feature is the constant one, the selected bit, or the product of the selected two bits. The coordinate carrier uses Schedule L as an index set; it does not replace the words or their first-zero classes.

**Definition 1.2 (Actual full-cube moments).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.moments`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.moments` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and arbitrary real measure mu on the raw Boolean cube, moments mu sums mu times feature in each constant, singleton and ordered pair coordinate.

**Definition 1.3 (Actual first-zero moment cone).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.MomentCone`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.MomentCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, first-zero address i and complete quadratic vector v, MomentCone i v means that one actual nonnegative real measure on the entire cube represents v and vanishes outside the original class FirstZero i. No relaxation to independent marginal data is made.

**Definition 1.4 (Baseline mass in each first-zero class).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.classBaselineMass`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.classBaselineMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y and address i, classBaselineMass sums A+P over precisely the original class FirstZero i. Terminal T is separate.

**Definition 1.5 (The coupled common-P constraints).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.CoupledFeasible`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.CoupledFeasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, full score y and families x,p of complete quadratic vectors indexed by every first-zero class, CoupledFeasible requires p, x-p and moments(numerical y i)-p to lie in the corresponding actual MomentCone; x's constant coordinate equals classBaselineMass; and the sum of all x vectors plus T times the terminal feature equals moments(baseline y). The same p is used in both differences, and the last equation is one aggregate equation on the common cube.

**Definition 1.6 (All feasible common masses).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.commonMassSet`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.commonMassSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, commonMassSet contains exactly the sums of constant coordinates of p over all x,p satisfying CoupledFeasible. It includes all actual feasible variables and retains a single shared P vector for each class.

**Definition 1.7 (The coupled optimum J).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.jointMaximum`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.jointMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, jointMaximum is the supremum of commonMassSet. The theorem below proves that this supremum is an attained greatest element equal to zero for the four-word family.

**Definition 1.8 (The original coefficient floor).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientFloor`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientFloor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, coefficientFloor is T plus the sum over every first-zero class of the maximum of its baseline mass and its numerical-label mass. It is K floor in Definition 213.7 and Theorem 213.8.

**Definition 1.9 (All actual fiber coefficient masses).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.fiberMassSet`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.fiberMassSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, fiberMassSet consists of coefficientMass z for all arbitrary nonnegative full scores z with the same beta as y and the same baseline and numerical mass on every output fiber of every original stopped Catalog function. The proved equivalence with SameFiber preserves exactly the original individual cell-label rewards. All raw words, first-zero classes and original individual rewards remain constrained.

**Definition 1.10 (The fiber coefficient minimum).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientMinimum`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientMinimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and full score y, coefficientMinimum is the infimum of fiberMassSet. The theorem below supplies a least element and an actual attaining score for this family, without assuming Theorem 213.8.

**Theorem 1.11 (Complete N and O costs).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_costs`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_costs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, ordered zero-based addresses n<j<k<l, late address n.val>=2 and positive real t, let y be witnessScore. Its entire beta function is 2t at n and zero elsewhere, its original anchor is t, and both complete supports are 3t and both complete costs are 2t. For every original schedule, every N or O cell and every empty cell, numerical label n+1 dominates the zero-label reward. The proof uses the whole-function Catalog correspondence for the support and for native output-fiber numerical dominance, identifies the reference-head functional with the anchor formula, bounds every label choice in every complete table and exhibits the constant numerical-label table attaining 3t; it uses no restriction on competitor supports.

**Theorem 1.12 (Attained joint and coefficient extrema).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_cone_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_cone_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L, n<j<k<l and positive real t, let y be witnessScore. Zero is a greatest element of commonMassSet and jointMaximum is zero. For all actual feasible x,p, every vector p i is zero. The value 4t is a least element of fiberMassSet, coefficientMinimum is 4t, coefficientFloor is 3t and the floor is strictly smaller than the minimum. An explicit feasible choice takes x at class n to be the moments of the actual base point of mass t, all other x to be zero and the shared p to be zero in every class. The source score itself attains the coefficient minimum. The cone proof chooses one P measure, one A residual and one C residual for each class, assembles the aggregate baseline, and applies the same nonnegative quadratic support separation. Direct polynomial formulas recover actual stopped readings from the complete moment vector; no general attainment or independent-P reconstruction theorem is assumed.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.CoupledFeasible`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.MomentCone`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.classBaselineMass`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientFloor`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.coefficientMinimum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.commonMassSet`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.feature`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.fiberMassSet`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.jointMaximum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.moments`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_cone_minimum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.proposition21310_costs`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog](JointRewardFiberCatalog.md)
