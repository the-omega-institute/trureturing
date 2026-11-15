# Core Base Model

## Abstract

Addressed quantum circuit: Core Base Model

**Definition 1.1 (classicalCoordinateDecidableEq).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalCoordinateDecidableEq`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalCoordinateDecidableEq` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every execution model, this instance supplies decidable equality on its classical-operation coordinates.

**Definition 1.2 (classicalOracleCoordinateDecidableEq).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalOracleCoordinateDecidableEq`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalOracleCoordinateDecidableEq` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every execution model, this instance supplies decidable equality on its classical-oracle coordinates.

**Definition 1.3 (gateCoordinateDecidableEq).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.gateCoordinateDecidableEq`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.gateCoordinateDecidableEq` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every execution model, this instance supplies decidable equality on its gate coordinates.

**Definition 1.4 (oracleCoordinateDecidableEq).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.oracleCoordinateDecidableEq`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.oracleCoordinateDecidableEq` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every execution model, this instance supplies decidable equality on its unitary-oracle coordinates.

**Definition 1.5 (systemDimensionDecidableEq).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.systemDimensionDecidableEq`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.systemDimensionDecidableEq` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every execution model, this instance supplies decidable equality on the dimensions of its systems.

**Definition 1.6 (ExecutionModel).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.ExecutionModel`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.ExecutionModel` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The operation language shared by an implementation and its specification.

**Definition 1.7 (classicalOperations).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalOperations`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalOperations` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The chosen classical native language is present in pure and hybrid execution.

**Definition 1.8 (classicalOracles).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalOracles`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalOracles` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The classical oracle service declaration is independent of every other language.

**Definition 1.9 (ClassicalCoordinate).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.ClassicalCoordinate`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.ClassicalCoordinate` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Model-owned native coordinates for actual classical instructions.

**Definition 1.10 (ClassicalOracleCoordinate).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.ClassicalOracleCoordinate`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.ClassicalOracleCoordinate` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Independently owned coordinates for actual classical oracle queries.

**Definition 1.11 (GateCoordinate).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.GateCoordinate`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.GateCoordinate` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Native gate coordinates are absent from classical execution.

**Definition 1.12 (OracleCoordinate).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.OracleCoordinate`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.OracleCoordinate` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Query coordinates are absent from classical execution and independent of native gates.

**Definition 1.13 (SystemDimension).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.SystemDimension`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Model.SystemDimension` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Fixed preparation and measurement dimensions exist only in quantum execution.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.ClassicalCoordinate`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.ClassicalOracleCoordinate`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.ExecutionModel`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.GateCoordinate`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.OracleCoordinate`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.SystemDimension`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalCoordinateDecidableEq`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalOperations`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalOracleCoordinateDecidableEq`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.classicalOracles`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.gateCoordinateDecidableEq`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.oracleCoordinateDecidableEq`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Model.systemDimensionDecidableEq`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Model](Classical/Model.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Oracle](Classical/Oracle.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model](Gate/Model.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Oracle/Model](Oracle/Model.md)
