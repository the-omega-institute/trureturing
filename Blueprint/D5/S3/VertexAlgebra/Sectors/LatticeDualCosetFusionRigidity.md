# Ground evaluation is injective for full dual-coset fields

## Abstract

LatticeDualCosetFusionRigidity

All entries quantify over arbitrary finite-rank symmetric even integral LatticeData D, including rank zero. Charge D is the original integral charge lattice; Carrier D is the complete finitely supported charge carrier with polynomial oscillators. a,b are integral module parameters, H is a complex matrix, and I is an arbitrary source-linear rational Hahn field. mode(I,u,tau) is raw coefficient -tau-1. Whenever stated, the full hypotheses are Lawful D a b H I, H G_C=1 and G_C H=1, rational mu,nu and exact duality G_Q mu=a, G_Q nu=b. Positivity and integral unimodularity are not assumed. The acting algebra and all module actions, cocycle and original conformal state are the actual native ones.

Classical lattice-fusion conventions follow Bakalov--Kac, math/0402315v1, section 4.1. Imported residue and Pascal suppliers retain Scott Carnahan, ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea; imported Sugawara suppliers retain Kalle Kytölä, VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. Both suppliers retain their Apache-2.0 attributions. These are native applications and proofs of classical mathematics; no literature novelty is claimed.

**Definition 1.1 (groundEvaluation).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.groundEvaluation`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.groundEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,a,b,H and rational mu,nu, this complex linear map sends J in operatorSpace D a b H to groundScalar D J.val mu nu 0 0, at old source/input charge zero and raw power pairing(mu,nu). The definition needs no inverse or duality hypotheses; injectivity needs both. Linearity follows from coefficient evaluation and polynomial constantCoeff.

**Theorem 1.2 (charged_source_recurrence).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.charged_source_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.charged_source_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full hypotheses, for all integral m,n,l, epsilon(D,m,n) groundScalar(m+n,l)=epsilon(D,m,n+l) groundScalar(n,l). In full charged Jacobi choose p=-C, r=-A-1 and tau=-Q-1, where A=chargedPower(a,m,n), C=chargedPower(b,m,l), Q=groundPower(mu,nu,n,l). The charged leading modes and ground lower bound reduce left and first sums to their zero terms and kill the second sum. This relates actual source charges, with no chosen nonzero operator. Used by ground_normalization_character.

**Theorem 1.3 (charged_input_recurrence).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.charged_input_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.charged_input_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full hypotheses, for all integral m,n,l, epsilon(D,m,n+l) groundScalar(n,l)=residueEpsilon(-chargedPower(a,m,n)) epsilon(D,m,l) groundScalar(n,m+l). Set p=-C-1, r=-A, tau=-Q-1 in full charged Jacobi. The left sum vanishes and the other two reduce to their leading terms. The residue sign is (-1) to the indicated integer power and is distinct from the lattice cocycle. Used by ground_normalization_character.

**Theorem 1.4 (ground_normalization_character).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.ground_normalization_character`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.ground_normalization_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full hypotheses, for all n,l, groundScalar(n,l)=epsilon(D,n,l) paritySign(sum_i l_i a_i) groundScalar(0,0). Here paritySign is 1 for even input and -1 for odd input. First propagate along the input from (0,0), then along the source; retain the original lattice cocycle. A zero normalized scalar propagates to all charge pairs. Used by normalized_ground_detects_zero.

**Theorem 1.5 (pair_ground_detects_zero).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.pair_ground_detects_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.pair_ground_detects_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full hypotheses, for every integral n,l, groundScalar(n,l)=0 implies that EVERY rational raw coefficient (I(ground n)).coeff s (ground l) vanishes. Well-founded induction on the actual partially well-ordered Hahn coefficient support uses positive-current Ward identities to annihilate all positive currents of a putative first nonzero coefficient. The imported scalar_of_positive_currents makes its charge component scalar; ground_spectrum then forces its raw power to the designated ground power, contradicting the zero scalar. No global integer lower bound on the rational support is assumed. This gives entire ground-pair Hahn vanishing from one scalar and is used by normalized_ground_detects_zero.

**Theorem 1.6 (ground_sequence_detects_zero).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.ground_sequence_detects_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.ground_sequence_detects_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary D,a,b,H and Lawful I, if for ALL integral n,l and rational mode tau, mode I (ground n) tau (ground l)=0, then I=0 as a full source-linear Hahn field. No inverse or rational duality is required here. Private reconstruct_input inducts over input oscillator polynomials using negative-current Ward; private reconstruct_source inducts over source polynomials using full Jacobi at p=0 and a negative current mode. Finite charge linear induction and coefficient extensionality recover all source and input states and all rational coefficients. This reconstructs the full field from its whole ground sequence and is used by normalized_ground_detects_zero.

**Theorem 1.7 (normalized_ground_detects_zero).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.normalized_ground_detects_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.normalized_ground_detects_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full hypotheses, groundScalar(mu,nu,0,0)=0 implies I=0 in the entire Fields D ambient space. Combine the charged normalization character, pair_ground_detects_zero and ground_sequence_detects_zero. This uses full arbitrary-charged Jacobi and actual actions and translations. No canonical, nonzero or pre-normalized field is assumed. Used by groundEvaluation_injective.

**Theorem 1.8 (groundEvaluation_injective).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.groundEvaluation_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.groundEvaluation_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,a,b,H, both inverse equations, rational mu,nu and exact dualities G_Q mu=a, G_Q nu=b, the complex linear map groundEvaluation from operatorSpace D a b H to Complex is injective. There is no separate fixed I or hI binder: its argument J carries the full lawful proof. Kernel triviality is normalized_ground_detects_zero applied to J.val. This is an upper bound only; it does not construct a nonzero element, prove existence or assert dimension exactly one. This is the resulting upper-bound consequence of normalized_ground_detects_zero.

pair_ground_detects_zero and ground_sequence_detects_zero derive scalar detection and full oscillator reconstruction, which normalized_ground_detects_zero combines to prove groundEvaluation_injective. Private mode_leading and mode_below reindex ground_leading and ground_below for both charged recurrences, using the charge and energy restrictions of ground_spectrum. Private reconstruct_input and reconstruct_source contain the oscillator inductions used by ground_sequence_detects_zero. The result permits the lawful space to be zero. A nonzero construction, existence, exact dimension one, categorical associativity or braiding, analytic/CFT realization and any string-theory completion remain outside these statements.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.charged_input_recurrence`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.charged_source_recurrence`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.groundEvaluation`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.groundEvaluation_injective`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.ground_normalization_character`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.ground_sequence_detects_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.normalized_ground_detects_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity.pair_ground_detects_zero`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner](LatticeDualCosetIntertwiner.md)
