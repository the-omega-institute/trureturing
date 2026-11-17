# Core Base WireAddress

## Abstract

Addressed quantum circuit: Core Base WireAddress

**Definition 1.1 (bitIndex).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bitIndex`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bitIndex` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Big-endian bit index for a physical wire; wire zero is most significant.

**Lemma 1.2 (bitIndex injective).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bitIndex_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bitIndex_injective` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma bitIndex_injective {n : Nat} : Function.Injective (bitIndex (n.

**Definition 1.3 (littleEndianWire).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.littleEndianWire`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.littleEndianWire` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Convert a little-endian index to the library's big-endian wire address.

**Lemma 1.4 (bitIndex littleEndianWire).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bitIndex_littleEndianWire`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bitIndex_littleEndianWire` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma bitIndex_littleEndianWire {n : Nat} (bit : Fin n) : bitIndex (littleEndianWire bit) = bit.

**Definition 1.5 (flipBit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.flipBit`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.flipBit` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Flip one addressed wire of a computational-basis label.

**Lemma 1.6 (bit flipBit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bit_flipBit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bit_flipBit` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma bit_flipBit {n : Nat} (target bit : Fin n) (x : Fin (2 ^ n)) : (flipBit target x).val.testBit (bitIndex bit).val = (x.val.testBit (bitIndex bit).val ^^ decide (target = bit)).

**Lemma 1.7 (bit flipBit self).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bit_flipBit_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bit_flipBit_self` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma bit_flipBit_self {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) : (flipBit target x).val.testBit (bitIndex target).val = !x.val.testBit (bitIndex target).val.

**Lemma 1.8 (bit flipBit of ne).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bit_flipBit_of_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bit_flipBit_of_ne` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma bit_flipBit_of_ne {n : Nat} {target bit : Fin n} (hne : target ≠ bit) (x : Fin (2 ^ n)) : (flipBit target x).val.testBit (bitIndex bit).val = x.val.testBit (bitIndex bit).val.

**Lemma 1.9 (flipBit flipBit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.flipBit_flipBit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.flipBit_flipBit` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma flipBit_flipBit {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) : flipBit target (flipBit target x) = x.

**Definition 1.10 (xMap).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.xMap`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.xMap` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Addressed X action.

**Definition 1.11 (xPerm).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.xPerm`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.xPerm` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Addressed X basis-label permutation.

**Definition 1.12 (cnotMap).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.cnotMap`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.cnotMap` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Addressed CNOT action.

**Lemma 1.13 (cnotMap cnotMap).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.cnotMap_cnotMap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.cnotMap_cnotMap` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma cnotMap_cnotMap {n : Nat} {control target : Fin n} (hct : control ≠ target) (x : Fin (2 ^ n)) : cnotMap control target (cnotMap control target x) = x.

**Definition 1.14 (cnotPerm).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.cnotPerm`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.cnotPerm` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Addressed CNOT basis-label permutation.

**Definition 1.15 (toffoliMap).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.toffoliMap`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.toffoliMap` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Addressed Toffoli action.

**Lemma 1.16 (toffoliMap toffoliMap).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.toffoliMap_toffoliMap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.toffoliMap_toffoliMap` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma toffoliMap_toffoliMap {n : Nat} {controlA controlB target : Fin n} (ha : controlA ≠ target) (hb : controlB ≠ target) (x : Fin (2 ^ n)) : toffoliMap controlA controlB target (toffoliMap controlA controlB target x) = x.

**Definition 1.17 (toffoliPerm).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.toffoliPerm`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.toffoliPerm` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Addressed Toffoli basis-label permutation; pairwise-distinctness witnesses certify the three wire roles while the permutation uses the two control-target inequalities.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bitIndex`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bitIndex_injective`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bitIndex_littleEndianWire`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bit_flipBit`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bit_flipBit_of_ne`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.bit_flipBit_self`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.cnotMap`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.cnotMap_cnotMap`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.cnotPerm`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.flipBit`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.flipBit_flipBit`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.littleEndianWire`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.toffoliMap`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.toffoliMap_toffoliMap`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.toffoliPerm`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.xMap`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress.xPerm`
