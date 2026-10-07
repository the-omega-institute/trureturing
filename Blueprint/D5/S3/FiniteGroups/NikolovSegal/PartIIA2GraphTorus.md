# Part II A2GraphTorus

## Abstract

Part II A2GraphTorus.

**Theorem 1.1 (tau coe).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_coe`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual graph automorphism sends g to its inverse transpose with both matrix indices reversed by Fin.revPerm.

**Theorem 1.2 (tau involutive).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the inverse-transpose and reversed-index graph automorphism twice returns the original determinant-one matrix, over every field.

**Theorem 1.3 (tau sq).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_sq`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual graph automorphism tau has square equal to the identity automorphism.

**Theorem 1.4 (tau T01).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T01`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T01` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph automorphism sends the actual (0,1) transvection with parameter t to the (1,2) transvection with parameter -t.

**Theorem 1.5 (tau T12).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T12`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph automorphism sends the actual (1,2) transvection with parameter t to the (0,1) transvection with parameter -t.

**Theorem 1.6 (tau T02).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T02`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T02` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph automorphism sends the central (0,2) transvection with parameter t to the same root with parameter -t.

**Theorem 1.7 (H coe).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_coe`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero lambda, the determinant-one torus element H is the actual diagonal matrix with entries lambda^2, lambda inverse, lambda inverse.

**Theorem 1.8 (H det).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_det`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero lambda, the diagonal matrix with entries lambda^2, lambda inverse, lambda inverse has determinant one.

**Theorem 1.9 (H inv coe).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_inv_coe`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_inv_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse of H(lambda) has diagonal entries (lambda inverse)^2, lambda, lambda.

**Theorem 1.10 (H conj T01).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T01`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T01` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by H(lambda), for nonzero lambda, multiplies the actual (0,1) root parameter by lambda^3.

**Theorem 1.11 (H conj T12).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T12`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by H(lambda), for nonzero lambda, fixes every actual (1,2) transvection.

**Theorem 1.12 (H conj T02).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T02`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T02` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by H(lambda), for nonzero lambda, multiplies the central (0,2) root parameter by lambda^3.

**Theorem 1.13 (isolating graph square).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.isolating_graph_square`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.isolating_graph_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a genuine automorphism exchanges the two simple roots with parameters chi0*phi(t) and chi1*phi(t). For nonzero lambda, the square of conj(H(lambda))*beta acts on the first simple root by lambda^3*chi1*phi(chi0)*phi^2(t). The same field automorphism and both signed root transports are retained.

**Theorem 1.14 (isolating tau square T01).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.isolating_tau_square_T01`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.isolating_tau_square_T01` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual graph automorphism tau and nonzero lambda, the square of conj(H(lambda))*tau sends the first simple-root parameter t to lambda^3*t.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_coe`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T01`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T02`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_conj_T12`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_det`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.H_inv_coe`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.isolating_graph_square`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.isolating_tau_square_T01`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T01`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T02`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_T12`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_coe`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_involutive`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus.tau_sq`
