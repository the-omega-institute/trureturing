# The augmented acyclic carrier theorem

## Abstract

Homotopies carried by basis-indexed acyclic subcomplexes.

**Definition 1.1 (Basis-indexed carriers).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.CarrierData`

*Formalization.* `D5/S3/HomologicalAlgebra/AcyclicCarrier.CarrierData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

For an arbitrary commutative ring R, nonnegative ModuleCat chain complexes C and D, an arbitrary family of index types I(n), and bases B(n) of C(n), a carrier assigns submodules A(n,b)(m) of D(m). The target differential preserves each carrier. If c has nonzero coefficient in the basis expansion of the boundary of b, every degree of the carrier of c lies in the corresponding degree of the carrier of b.

**Definition 1.2 (Carried linear maps).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.Carried`

*Formalization.* `D5/S3/HomologicalAlgebra/AcyclicCarrier.Carried` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

A map from C(n) to D(m) is carried when the image of every basis vector b belongs to A(n,b)(m).

**Definition 1.3 (Augmented carrier acyclicity).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.Acyclic`

*Formalization.* `D5/S3/HomologicalAlgebra/AcyclicCarrier.Acyclic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

The augmentation may take values in an arbitrary R-module. It vanishes on boundaries. In each individual carrier, augmentation-zero elements in degree zero lift to degree one, and cycles in every positive degree lift to the next degree. No contraction or chosen lift is assumed.

**Theorem 1.4 (Finite-support boundary extension).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.face`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.face` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

A carried linear map sends the boundary of each source basis vector into the carrier of that vector. Expand the boundary using Basis.repr, sum only over its finite support, apply coefficient-support nesting to each term, and use closure of the target submodule under scalar multiplication and finite sums.

**Theorem 1.5 (Subtraction preserves bounds).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.sub`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

The difference of two maps carried in the same degrees remains carried.

**Theorem 1.6 (Support-preserving basis lift).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.basis_exists_lift`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.basis_exists_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

For any target linear map phi and basis-indexed source map Phi, if every Phi(B(b)) has a preimage in its specified submodule, choose those preimages and extend along the source basis. The extension is carried and its composite with phi equals Phi by basis extensionality. The basis can be empty or infinite, and neither target has a basis requirement.

**Theorem 1.7 (Positive-degree primitive).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_primitive`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_primitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

A carried map into positive-degree cycles lifts through the target differential with the same individual carrier bounds. Extend the carrier primitives along the source basis.

**Theorem 1.8 (Augmentation-zero primitive).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_primitive0`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_primitive0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

A carried degree-zero map annihilated by the augmentation lifts to degree one with the same carrier bounds. Extend the degree-zero primitives along the source basis.

**Theorem 1.9 (Integer scaling preserves bounds).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.comp_left`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.comp_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

Integer multiples of carried maps remain carried.

**Theorem 1.10 (Boundary precomposition).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.d_comp`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.d_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

Precomposing a carried map with the source boundary preserves the shifted carrier bound. The finite-support boundary expansion gives the bound.

**Theorem 1.11 (Dependent sequence of primitive choices).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_sequence`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_sequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

Given an initial state and an allowed successor for every state in every degree, dependent recursion produces a sequence satisfying the initial and successor predicates.

**Theorem 1.12 (Carried component induction).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_homotopy`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_homotopy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

For an arbitrary integer sign and two carried component families obeying the corresponding twisted chain equations and equal augmentation, degree induction constructs carried homotopy components. The state includes the residual cycle condition. Degree zero uses an augmentation-zero primitive; each successor subtracts the preceding homotopy on the source boundary, verifies that the residual is a cycle using the chain equations, and chooses a carrier primitive.

**Theorem 1.13 (Native carried chain homotopy).**

Lean statement: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_homotopy`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_homotopy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

For every commutative ring R, arbitrary nonnegative ModuleCat chain complexes C and D, and arbitrary bases B(n) indexed by I(n), assume differential-closed basis-indexed carriers, nesting for every nonzero coefficient of each source basis boundary, and augmented acyclicity separately in every carrier. For every pair of chain maps f and g that agree after the augmentation D(0) to R and carry B(n)(b) into A(n,b)(n), there exists a native Homotopy f g whose component H.hom n (n+1) sends B(n)(b) into A(n,b)(n+1). The ring, module and index universes are arbitrary. The theorem permits zero rings, empty and infinite source bases, and non-surjective augmentations, and imposes no target basis, target projectivity, source acyclicity, global contractibility or homotopy-as-input hypothesis. The native Homotopy equations give f(0)-g(0)=dH(0), and f(n+1)-g(n+1)=dH(n+1)+H(n)d in positive degrees. The signed component construction with sign one gives the native Homotopy with exactly these carrier bounds.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.Acyclic`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.Carried`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.CarrierData`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.basis_exists_lift`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.comp_left`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.d_comp`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_homotopy`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_primitive`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_primitive0`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_homotopy`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_sequence`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.face`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.sub`
