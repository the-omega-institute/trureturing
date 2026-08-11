# Address-Record Correlation Monogamy

## Abstract

A perfect Z-address copy in one fixed record pointer eliminates its conjugate X correlation.

**Theorem 1.1 (A perfect address copy eliminates conjugate correlation).**

$$\forall \rho,\ \operatorname{PosSemidef}(\rho) \land \operatorname{Tr}(\rho)=1 \land C_{Z}(\rho)=1 \Rightarrow\\C_{X}(\rho)=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RecordCorrelationMonogamy.record_correlation_monogamy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be an arbitrary positive semidefinite trace-one matrix on a system qubit and a two-address record. No diagonal, separable, or classical-mixture hypothesis is imposed. The record observable remains its fixed address pointer Z_R. For a system observable A, define C_A(rho) as the real part of Tr(rho(A tensor Z_R)). Thus C_Z tests an address copy and C_X tests the conjugate system observable against the same physical pointer.

If C_Z(rho)=1, trace normalization and positivity force both mismatched address populations to vanish. For a positive semidefinite matrix, zero weight on a basis vector forces its entire row and column to vanish. Every nonzero matrix entry of X tensor Z_R joins an agreeing address basis vector to a mismatched one, so all four terms in C_X vanish. This is the structural no-cloning step carried by the theorem.

The fixed-pointer clause is essential. Defining the second quantity as Tr(rho(X tensor X)) would make the proposed implication false: a Bell state has both Z-tensor-Z and X-tensor-X correlation equal to one. The theorem makes no diagonal-state restriction and no false Bell-state claim; it states what one classical address pointer can record.

**Theorem 1.2 (A non-diagonal state has nonzero conjugate correlation).**

$$\operatorname{PosSemidef}(\rho_{+0}) \land \operatorname{Tr}(\rho_{+0})=1 \land\\\rho_{+0}(00,10)=\frac{1}{2} \land C_{Z}(\rho_{+0})=0 \land C_{X}(\rho_{+0})=1.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RecordCorrelationMonogamy.coherent_record_anti_vacuity_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product state rho_(+0)=|+0><+0| is positive semidefinite and trace one. Its (00,10) entry is 1/2, so it is explicitly non-diagonal. It has C_Z=0 and C_X=1 against the fixed record pointer. Therefore C_X is not identically zero on the theorem's general domain; the main implication uses the perfect-copy premise.

**Theorem 1.3 (A noisy address record has three-quarter correlation).**

$$\operatorname{PosSemidef}(\rho_{\frac{3}{4}}) \land \operatorname{Tr}(\rho_{\frac{3}{4}})=1 \land\\C_{Z}(\rho_{\frac{3}{4}})=\frac{3}{4} \land C_{X}(\rho_{\frac{3}{4}})=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RecordCorrelationMonogamy.three_quarter_address_record_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerical witness assigns 7/16 to each agreeing address pair and 1/16 to each disagreeing pair. Its diagonal embedding is a positive trace-one state with C_Z=3/4 and C_X=0. This explicit leg remains separate from the general-state theorem and supplies the requested nontrivial numerical reading.

## References

- Truth anchor: `D5/S3/ObserverMemory/RecordCorrelationMonogamy.coherent_record_anti_vacuity_certificate`
- Truth anchor: `D5/S3/ObserverMemory/RecordCorrelationMonogamy.record_correlation_monogamy`
- Truth anchor: `D5/S3/ObserverMemory/RecordCorrelationMonogamy.three_quarter_address_record_certificate`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../Quantum/FiniteDimensional.md)
