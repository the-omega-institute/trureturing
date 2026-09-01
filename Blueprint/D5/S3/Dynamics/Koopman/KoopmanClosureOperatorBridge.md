# Koopman Closure Operator Bridge

## Abstract

Existing observable Koopman generators are exactly finite iterates of the first-class discrete Koopman operator.

**Definition 1.1 (Operator-generated Koopman observables).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.operatorKoopmanGenerators`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.operatorKoopmanGenerators` (`✓ std3`).

**Theorem 1.2 (Operator and existing generators coincide).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.operatorKoopmanGenerators_eq_existing`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.operatorKoopmanGenerators_eq_existing` (`✓ std3`). ∎

**Theorem 1.3 (Existing closure is the operator-iterate adjoin).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.koopmanClosure_eq_adjoin_operatorIterates`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.koopmanClosure_eq_adjoin_operatorIterates` (`✓ std3`). ∎

**Theorem 1.4 (Source observables enter at depth zero).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.sourceObservable_mem_operatorKoopmanGenerators`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.sourceObservable_mem_operatorKoopmanGenerators` (`✓ std3`). ∎

**Theorem 1.5 (Further pullback advances generator depth).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.koopmanIterate_succ_mem_operatorKoopmanGenerators`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.koopmanIterate_succ_mem_operatorKoopmanGenerators` (`✓ std3`). ∎

## References

- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.operatorKoopmanGenerators`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.operatorKoopmanGenerators_eq_existing`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.koopmanClosure_eq_adjoin_operatorIterates`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.sourceObservable_mem_operatorKoopmanGenerators`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanClosureOperatorBridge.koopmanIterate_succ_mem_operatorKoopmanGenerators`
- Dependency: [D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator](DiscreteKoopmanOperator.md)
- Dependency: [D5/S3/QuantumStates/ObservableAlgebraClosureDuality](../../QuantumStates/ObservableAlgebraClosureDuality.md)
