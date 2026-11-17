# Util FinPow BinaryBasis Pair

## Abstract

Addressed quantum circuit: Util FinPow BinaryBasis Pair

**Lemma 1.1 (bigEndianEquiv cons value).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair.bigEndianEquiv_cons_value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair.bigEndianEquiv_cons_value` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma bigEndianEquiv_cons_value (n : Nat) (head : Fin 2) (tail : Fin n → Fin 2) : (bigEndianEquiv (n + 1) (Fin.cons head tail)).val = (bigEndianEquiv n tail).val + 2 ^ n * head.val.

**Lemma 1.2 (bigEndianEquiv cons pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair.bigEndianEquiv_cons_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair.bigEndianEquiv_cons_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma bigEndianEquiv_cons_pair (n : Nat) (head : Fin 2) (tail : Fin n → Fin 2) : bigEndianEquiv (n + 1) (Fin.cons head tail) = qftPairEquiv n (head, bigEndianEquiv n tail).

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair.bigEndianEquiv_cons_pair`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair.bigEndianEquiv_cons_value`
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow](../../FinPow.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis](../BinaryBasis.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse](../BitReverse.md)
