# Physical current jet finite differences

## Abstract

Physical current jet finite differences

All operators are the unrestricted original half-integer tensor currents and charged coefficient slices. No positive Gram form, rank constraint, inverse matrix or locality premise is introduced.

**Theorem 1.1 (The original negative Ward shift gives the physical parity carry).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_charge_ward`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_charge_ward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The commutator at physical modes m and k is the original charge pairing times the opposite parity slice at mode k plus m plus parity. The cover law uses exponent minus two times m minus one. Increasing either physical input mode by one therefore produces exactly the same commutator, so one ordinary delta kills it.

**Theorem 1.2 (The actual jet of order r has charged locality order r plus one).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_charge_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_charge_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The proof uses the actual factorial-normalized jetScalar successor identity and a proved iterated finite-difference Leibniz identity. Multiplication by a linear mode factor raises an already established killing order by one. This is not an appeal to polynomial-degree intuition.

**Theorem 1.3 (The actual jet pair of orders r and s has locality order r plus s plus two).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_pair_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_pair_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The tensor Heisenberg commutator retains support on m plus n plus one equal to zero and its coefficient m plus one half times the Gram entry. Its second difference is proved directly on that diagonal; the two jet orders are then added by the same finite-difference identity and the existing ordinary symmetry theorem. The source lattice VOA is bosonic throughout.

Full four-slot escape registration and publication are distinct from kernel checking. The larger twisted Jacobi, fusion, anomaly and string/AdS objectives remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_charge_ward`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_charge_locality`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_pair_locality`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateLocality](LatticeAllStateLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling](LatticeHalfFockPhysicalRescaling.md)
