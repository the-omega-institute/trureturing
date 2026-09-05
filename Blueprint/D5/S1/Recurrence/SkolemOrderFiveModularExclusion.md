# Order-Five Skolem Modular Exclusion

## Abstract

A certified period-thirty-one parity orbit excludes zeros in sixteen residue classes for an infinite congruence class of order-five integer recurrences.

**Definition 1.1 (Five-coordinate parity state).**

$$\operatorname{State} = (x0: \operatorname{ZMod}(2) , x1: \operatorname{ZMod}(2) , x2: \operatorname{ZMod}(2) , x3: \operatorname{ZMod}(2) , x4: \operatorname{ZMod}(2)).$$

*Formalization.* `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

State has exactly five coordinates, each valued in ZMod(2).

**Definition 1.2 (Parity companion step).**

$$\forall s: \operatorname{State}, \operatorname{step}(s) = (s.x1 , s.x2 , s.x3 , s.x4 , s.x0 + s.x3).$$

*Formalization.* `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The step shifts four coordinates and adds the old zeroth and third coordinates in the final position.

**Definition 1.3 (Prescribed coefficient residues).**

$$\operatorname{coeffBits} = (1 , 0 , 0 , 1 , 0).$$

*Formalization.* `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.coeffBits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five recurrence coefficients reduce to the displayed bit vector.

**Definition 1.4 (Prescribed initial residues).**

$$\operatorname{initialBits} = (1 , 0 , 0 , 0 , 0).$$

*Formalization.* `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.initialBits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first five sequence terms reduce to the displayed bit vector.

**Definition 1.5 (Initial parity state).**

$$\operatorname{initialState} = (1 , 0 , 0 , 0 , 0).$$

*Formalization.* `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.initialState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parity orbit begins at the state represented by the initial residues.

**Definition 1.6 (Order-five integer recurrence).**

$$\begin{aligned}\forall a: \operatorname{Fin}(5) \to \mathbb{Z}, u: \mathbb{N} \to \mathbb{Z},\\\operatorname{intRecurrence}(a).order = 5 \land \operatorname{intRecurrence}(a).coeffs = a,\\(\operatorname{IsSolution}(\operatorname{intRecurrence}(a) , u)) \Leftrightarrow\\\forall m \in \mathbb{N}, u_{m + 5} = \sum_{i \in \operatorname{Fin}(5)} a_{i} \cdot u_{m + \operatorname{val}(i)}.\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.intRecurrence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recurrence has order five and coefficient function a. Its IsSolution equation is the order-five recurrence from the candidate atom.

**Definition 1.7 (Coordinatewise parity reduction).**

$$\forall u: \mathbb{N} \to \mathbb{Z}, n \in \mathbb{N}, \operatorname{reducedState}(u , n) = (\operatorname{cast}(u_{n} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{n + 1} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{n + 2} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{n + 3} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{n + 4} , \operatorname{ZMod}(2))).$$

*Formalization.* `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.reducedState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Five consecutive integer terms are cast coordinatewise to ZMod(2).

**Definition 1.8 (Binary companion orbit).**

$$\forall n \in \mathbb{N}, \operatorname{orbitState}(n) = \operatorname{iterate}(step , n , (1 , 0 , 0 , 0 , 0)).$$

*Formalization.* `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.orbitState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nth orbit state is the nth iterate of step at the prescribed initial state.

**Definition 1.9 (Possible zero residues modulo thirty-one).**

$$\operatorname{possibleZeroResidues} = \left\{1, 2, 3, 4, 6, 8, 12, 15, 16, 17, 23, 24, 27, 29, 30\right\}.$$

*Formalization.* `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.possibleZeroResidues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the full fifteen-element exceptional residue set.

**Theorem 1.10 (Reduction modulo two commutes with the companion step).**

$$\begin{aligned}\forall a: \operatorname{Fin}(5) \to \mathbb{Z}, u: \mathbb{N} \to \mathbb{Z},\\(\operatorname{IsSolution}(\operatorname{intRecurrence}(a) , u)) \Rightarrow\\((\operatorname{cast}(a_{0} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{1} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{2} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{3} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{4} , \operatorname{ZMod}(2))) = (1 , 0 , 0 , 1 , 0)) \Rightarrow\\\forall n \in \mathbb{N}, \operatorname{reducedState}(u , n + 1) = \operatorname{step}(\operatorname{reducedState}(u , n)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.reduction_commutes_with_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For E_a of order five with coefficients a, reducedState(u,n) is the five-tuple of terms u_n through u_(n+4), each cast to ZMod(2). Under the displayed coefficient congruence, the IsSolution equation reduces its final coordinate to x_0+x_3, uniformly for every integer lift.

**Theorem 1.11 (The binary state orbit closes after thirty-one steps).**

$$\operatorname{iterate}(step , 31 , (1 , 0 , 0 , 0 , 0)) = (1 , 0 , 0 , 0 , 0).$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.orbit_closes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here s_0=(1,0,0,0,0) in ZMod(2)^5 and step sends (x_0,x_1,x_2,x_3,x_4) to (x_1,x_2,x_3,x_4,x_0+x_3). Ordinary kernel decision checks the closing edge.

**Theorem 1.12 (The binary state orbit has no early return).**

$$\forall k \in \operatorname{Fin}(30), \operatorname{iterate}(step , \operatorname{val}(k) + 1 , (1 , 0 , 0 , 0 , 0)) \neq (1 , 0 , 0 , 0 , 0).$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.orbit_no_early_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordinary kernel decision checks every positive iterate from one through thirty. Together with the closing edge, this certifies exact period thirty-one rather than merely a period dividing thirty-one.

**Theorem 1.13 (The first coordinate is one on the sixteen complementary residues).**

$$\begin{aligned}\forall r \in \operatorname{Fin}(31),\\(\neg (\operatorname{val}(r) \in \left\{1, 2, 3, 4, 6, 8, 12, 15, 16, 17, 23, 24, 27, 29, 30\right\})) \Rightarrow\\\operatorname{x0}(\operatorname{iterate}(step , \operatorname{val}(r) , (1 , 0 , 0 , 0 , 0))) = 1.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.orbit_nonzero_readoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exceptional set Z is exactly {1,2,3,4,6,8,12,15,16,17,23,24,27,29,30}. Ordinary kernel decision reads the first coordinate on every residue outside Z.

**Theorem 1.14 (Every term outside the exceptional residues is odd).**

$$\begin{aligned}\forall a: \operatorname{Fin}(5) \to \mathbb{Z}, u: \mathbb{N} \to \mathbb{Z},\\(\operatorname{IsSolution}(\operatorname{intRecurrence}(a) , u) \land (\operatorname{cast}(a_{0} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{1} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{2} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{3} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{4} , \operatorname{ZMod}(2))) = (1 , 0 , 0 , 1 , 0) \land (\operatorname{cast}(u_{0} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{1} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{2} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{3} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{4} , \operatorname{ZMod}(2))) = (1 , 0 , 0 , 0 , 0)) \Rightarrow\\\forall n \in \mathbb{N}, (\neg (n \bmod 31 \in \left\{1, 2, 3, 4, 6, 8, 12, 15, 16, 17, 23, 24, 27, 29, 30\right\})) \Rightarrow \operatorname{Odd}(u_{n}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.odd_of_mod31_not_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The commuting reduction identifies every lifted solution state with the certified binary orbit. IsPeriodicPt.iterate_mod_apply reduces n by the natural-number remainder modulo thirty-one, and the readout certificate makes the corresponding integer term odd.

**Theorem 1.15 (Uniform modular exclusion for order-five integer recurrences).**

$$\begin{aligned}\forall a: \operatorname{Fin}(5) \to \mathbb{Z}, u: \mathbb{N} \to \mathbb{Z},\\(\operatorname{IsSolution}(\operatorname{intRecurrence}(a) , u) \land (\operatorname{cast}(a_{0} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{1} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{2} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{3} , \operatorname{ZMod}(2)) , \operatorname{cast}(a_{4} , \operatorname{ZMod}(2))) = (1 , 0 , 0 , 1 , 0) \land (\operatorname{cast}(u_{0} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{1} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{2} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{3} , \operatorname{ZMod}(2)) , \operatorname{cast}(u_{4} , \operatorname{ZMod}(2))) = (1 , 0 , 0 , 0 , 0)) \Rightarrow\\(\forall n \in \mathbb{N}, (\neg (n \bmod 31 \in \left\{1, 2, 3, 4, 6, 8, 12, 15, 16, 17, 23, 24, 27, 29, 30\right\})) \Rightarrow \operatorname{Odd}(u_{n}))\\\land (\forall n \in \mathbb{N}, (u_{n} = 0) \Rightarrow n \bmod 31 \in \left\{1, 2, 3, 4, 6, 8, 12, 15, 16, 17, 23, 24, 27, 29, 30\right\}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.zero_index_mod31_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct is the uniform oddness statement on all sixteen complementary residue classes. The second is its zero-index consequence, so this single theorem states the whole candidate atom rather than covering only its final corollary.

The symbol n mod 31 denotes the natural-number remainder, represented by modulo notation rather than a fraction. This theorem does not decide whether a zero occurs in any of the fifteen exceptional classes and is not a decision procedure for the order-five Skolem problem.

## References

- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.State`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.coeffBits`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.initialBits`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.initialState`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.intRecurrence`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.odd_of_mod31_not_mem`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.orbitState`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.orbit_closes`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.orbit_no_early_return`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.orbit_nonzero_readoff`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.possibleZeroResidues`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.reducedState`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.reduction_commutes_with_step`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.step`
- Truth anchor: `D5/S1/Recurrence/SkolemOrderFiveModularExclusion.zero_index_mod31_mem`
