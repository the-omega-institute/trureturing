# Displacement and Beatty Forms of Golden Fiber Coordinates

## Abstract

Golden fiber coordinates have exact displacement forms, an equation characterizes each fiber, and the proposed ceiling start fails at label one.

**Theorem 1.1 (Both fiber coordinates have exact displacement forms).**

$$\forall v \in \mathbb{N},\ \operatorname{fiberA}(v) = 2 \cdot \operatorname{displacementDecode}(v) - 3 \cdot v \land \operatorname{fiberB}(v) = 2 \cdot v - \operatorname{displacementDecode}(v)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms.fiber_coordinates_eq_displacement_forms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural index v, the first golden fiber coordinate is twice the displacement reading minus three times v, while the second is twice v minus the same displacement reading.

The established Beatty formula for the displacement reading replaces the common golden-shift term in both coordinate definitions. Thus the two floor-defined coordinates and their integral linear forms agree simultaneously.

**Theorem 1.2 (Fiber membership is exactly the doubled displacement equation).**

$$\forall a \in \mathbb{Z}, v \in \mathbb{N},\ v \in \operatorname{goldenFiber}(a) \iff 2 \cdot \operatorname{displacementDecode}(v) = 3 \cdot v + a$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms.mem_goldenFiber_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fiber labelled by an integer a is the level set where the first coordinate equals a. An index v belongs to this fiber exactly when twice its displacement reading equals three times v plus a.

Substituting the first coordinate's displacement form turns the level-set condition into this equation without changing either direction of the equivalence.

**Theorem 1.3 (The proposed ceiling start fails at label one).**

$$\operatorname{ceil}(\varphi - \varphi^{2}) \neq \lfloor\varphi - \varphi^{2}\rfloor + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms.ceiling_start_formula_fails_at_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At label one, the golden-ratio square identity reduces phi minus phi squared to minus one. Its ceiling is therefore minus one, whereas its floor followed by adding one is zero, so the proposed ceiling start cannot equal the corrected floor-plus-one expression.

## References

- Truth anchor: `D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms.ceiling_start_formula_fails_at_one`
- Truth anchor: `D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms.fiber_coordinates_eq_displacement_forms`
- Truth anchor: `D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms.mem_goldenFiber_iff`
- Dependency: [D5/S1/Deficit/ZeckendorfDisplacementReading](../ZeckendorfDisplacementReading.md)
- Dependency: [D5/S1/Words/GoldenFiberCoordinates](../../Words/GoldenFiberCoordinates.md)
