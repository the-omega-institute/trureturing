# Polynomial pairing from one common input

## Abstract

Polynomial pairing from one common input.

The original input is saved before either transducer runs. The first result is framed, the original input is restored, and the second transducer receives that same word. The two results are assembled in their original order by PairConstructor. Actual simulations and physical output-size bounds prove a uniform polynomial tape runtime; all saved frame words survive normalization.

**Theorem 1.1 (simulationRegister_injective).**

Lean statement: `D5/S0/Computability/BinaryMachine/TransducerPair.simulationRegister_injective`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/TransducerPair.simulationRegister_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

The original input is saved before either transducer runs. The first result is framed, the original input is restored, and the second transducer receives that same word. The two results are assembled in their original order by PairConstructor. Actual simulations and physical output-size bounds prove a uniform polynomial tape runtime; all saved frame words survive normalization.

**Theorem 1.2 (exec_normalized).**

Lean statement: `D5/S0/Computability/BinaryMachine/TransducerPair.exec_normalized`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/TransducerPair.exec_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

The original input is saved before either transducer runs. The first result is framed, the original input is restored, and the second transducer receives that same word. The two results are assembled in their original order by PairConstructor. Actual simulations and physical output-size bounds prove a uniform polynomial tape runtime; all saved frame words survive normalization.

**Theorem 1.3 (exec_program).**

Lean statement: `D5/S0/Computability/BinaryMachine/TransducerPair.exec_program`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/TransducerPair.exec_program` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

The original input is saved before either transducer runs. The first result is framed, the original input is restored, and the second transducer receives that same word. The two results are assembled in their original order by PairConstructor. Actual simulations and physical output-size bounds prove a uniform polynomial tape runtime; all saved frame words survive normalization.

**Theorem 1.4 (polyTime_pair).**

Lean statement: `D5/S0/Computability/BinaryMachine/TransducerPair.polyTime_pair`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/TransducerPair.polyTime_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

The original input is saved before either transducer runs. The first result is framed, the original input is restored, and the second transducer receives that same word. The two results are assembled in their original order by PairConstructor. Actual simulations and physical output-size bounds prove a uniform polynomial tape runtime; all saved frame words survive normalization.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/TransducerPair.exec_normalized`
- Truth anchor: `D5/S0/Computability/BinaryMachine/TransducerPair.exec_program`
- Truth anchor: `D5/S0/Computability/BinaryMachine/TransducerPair.polyTime_pair`
- Truth anchor: `D5/S0/Computability/BinaryMachine/TransducerPair.simulationRegister_injective`
- Dependency: [D5/S0/Computability/BinaryMachine/Composition](Composition.md)
- Dependency: [D5/S0/Computability/BinaryMachine/PairConstructor](PairConstructor.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackCompile](StackCompile.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackFrame](StackFrame.md)
