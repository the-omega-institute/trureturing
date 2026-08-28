# Selective Record Conditioning

## Abstract

A nonzero record branch determines its normalized selective system state.

**Theorem 1.1 (A nonzero record branch forces the selective state).**

$$\forall n, K: \operatorname{Type}, [\operatorname{Fintype}(n)],\\{}P: K \to M_{n}(\mathbb{C}), \rho, \rho_{k}: M_{n}(\mathbb{C}),\\{}k \in K, \operatorname{Tr}\left(\rho P_{k}\right) \neq 0,\\{}\operatorname{Tr}\left(\rho P_{k}\right) \rho_{k} = P_{k} \rho P_{k} \Rightarrow\\{}\rho_{k} = \frac{P_{k} \rho P_{k}}{\operatorname{Tr}\left(\rho P_{k}\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/SelectiveRecordConditioning.selective_record_conditioning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a finite complex matrix and let P_k be the matrix selected by a record value k. The supplied branch law says that multiplying the conditioned state rho_k by its Born weight recovers the unnormalized compression P_k rho P_k.

When the Born weight is nonzero, scalar cancellation uniquely determines rho_k. The proof uses the field inverse law and scalar associativity; the conditioned state is not defined to be the displayed target.

## References

- Truth anchor: `D5/S3/Observer/Conditioning/SelectiveRecordConditioning.selective_record_conditioning`
- Dependency: [D5/S3/Observer/Conditioning](../Conditioning.md)
