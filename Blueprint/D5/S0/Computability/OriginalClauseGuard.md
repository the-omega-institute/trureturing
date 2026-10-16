# A finite lexical repair transducer

## Abstract

A finite lexical repair transducer.

The finite control is the original eleven-state unrestricted lexical phase. Each raw input bit causes one literal stack pop, followed by an empty pop and a halt. A saved copy restores every accepted word without changing any payload bit. A rejected phase installs the fixed fallback word by actual primitive pushes. The validity bit in this module is the ending phase of Unrestricted.scanPhase; relating it to the exact mathematical decoder is a separate source-semantic obligation. The supplied FinTM2 parser is not used as an execution certificate for this tape model.

**Theorem 1.1 (exec_scan).**

Lean statement: `D5/S0/Computability/OriginalClauseGuard.exec_scan`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/OriginalClauseGuard.exec_scan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

The finite control is the original eleven-state unrestricted lexical phase. Each raw input bit causes one literal stack pop, followed by an empty pop and a halt. A saved copy restores every accepted word without changing any payload bit. A rejected phase installs the fixed fallback word by actual primitive pushes. The validity bit in this module is the ending phase of Unrestricted.scanPhase; relating it to the exact mathematical decoder is a separate source-semantic obligation. The supplied FinTM2 parser is not used as an execution certificate for this tape model.

**Theorem 1.2 (polyTime_repair).**

$$\forall fallback \in \mathit{Word},\; \operatorname{PolyTime}\left(\operatorname{repair}\left(\mathit{fallback}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/OriginalClauseGuard.polyTime_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

The finite control is the original eleven-state unrestricted lexical phase. Each raw input bit causes one literal stack pop, followed by an empty pop and a halt. A saved copy restores every accepted word without changing any payload bit. A rejected phase installs the fixed fallback word by actual primitive pushes. The validity bit in this module is the ending phase of Unrestricted.scanPhase; relating it to the exact mathematical decoder is a separate source-semantic obligation. The supplied FinTM2 parser is not used as an execution certificate for this tape model.

## References

- Truth anchor: `D5/S0/Computability/OriginalClauseGuard.exec_scan`
- Truth anchor: `D5/S0/Computability/OriginalClauseGuard.polyTime_repair`
- Dependency: [D5/S0/Computability/BinaryMachine/StackCompile](BinaryMachine/StackCompile.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackControl](BinaryMachine/StackControl.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackPair](BinaryMachine/StackPair.md)
- Dependency: [D5/S0/Computability/OriginalClauseLanguages](OriginalClauseLanguages.md)
