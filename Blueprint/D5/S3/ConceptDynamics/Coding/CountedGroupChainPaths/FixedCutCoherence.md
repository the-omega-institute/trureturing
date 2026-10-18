# Complete records and reversible fixed cuts

## Abstract

Complete fixed-cut coherence for endpoint-preserving numbered group paths, with literal positive factors and the rational complement.

This is a reusable supplier for original sections 25.1–25.5, not a proof of that entire result. Its exact declarations are linked by owner handles. The current pinned projection corpus has no entries for this new module; the canonical emitter records that presentation gap instead of inventing a projected statement. The generic statements quantify over an arbitrary universe and finite ordered group H, arbitrary dimensions and group matrices, every displayed endpoint-preserving bijection, and every legal input of the displayed dependent type. Word and At keep actual H labels, independent parallel-copy numbers and every dependent endpoint. FlatOut keeps both boundary edges, their middle vertex and the entire output word. No scalar equality or independent witness replaces equality of these records.

**Definition 1.1 (A reversible cut at a prescribed position).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.concatEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.concatEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Concatenation and cut are inverse on legal fibre products. The zero-length case retains its named vertex; the successor proof reconstructs all numbered edges and their endpoints. No default edge is supplied for an incompatible seam.

**Definition 1.2 (The entire record is encoded with its fixed cut).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.encoding`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.encoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

First apply psi to the original left/right boundary pair, then concatenate the full output word. The inverse recovers both cuts and every original boundary coordinate.

**Theorem 1.3 (Record reconstruction).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.exact_fixed_cut`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.exact_fixed_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decoding an encoded FlatOut is the same record, including both boundary edges, labels, copies and endpoint vertices. This is an equivalence-law consequence of the constructed encoding.

**Theorem 1.4 (The local recurrence equals the two complete sweeps).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.run_path`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.run_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word length d, local fibre-product squares return exactly the full flatDouble record. Induction exchanges independent front and back operations with the common endpoints fixed. This is not an assumption that arbitrary adjacent functions commute.

**Theorem 1.5 (Finite inverse overlap forces literal one-edge alignment).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.finite_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.finite_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume FlatBalanced at positive lag L and an actual diagonal continuation edge at each source vertex. Apply the inverse-block law to overlapping finite blocks, use a legal repeated right continuation and recover the common prefix and final edge. The conclusion is Aligned for the same phi, chi and psi. Both positivity of lag and continuation remain explicit hypotheses; the six laws alone are not asserted sufficient.

**Theorem 1.6 (All-length equality of full output records).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.full_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.full_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the literal Aligned hypothesis, every finite d, including d=0, has flatDouble equal to fixedCutDouble on the same entire typed input. A whole-word invariant identifies the encoding before reversible decoding; this retains the output word as well as both cuts.

**Theorem 1.7 (Both inverse identities for the complete output).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.full_inverse_coherence`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.full_inverse_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same all-length equality gives both inverse directions on FlatInput and FlatOut. These are full dependent record identities, not just boundary or total-label identities.

**Definition 1.8 (The literal original A, U, V, T and D).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualAt`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Put q=card(H), u=sum of all group elements and z=q*1-u. In zero-based Fin n coordinates, T(i,j)=1 exactly when i+1=j and i<t-1; D(i,j)=1 exactly when i=j and i<t-1. The integer lifts are A_t=q^3*n*J*u+q*z*T_t, U_t=q*J*u+z*D_t and V_t=q*J*u+z*T_t; actualAt, actualU and actualV take coefficientwise toNat. These are the original coordinates, not similar matrices.

**Theorem 1.9 (All labels of both original factors are positive).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.factorPositive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.factorPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nontrivial H and every coordinate, both factors have positive coefficients. An inactive entry has coefficient q at every label. An active entry has 2q-1 at the unit and q-1 elsewhere. This directly reuses uniform_perturbation_positive.

**Theorem 1.10 (Both prescribed products use those same factors).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.prescribedProducts`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.prescribedProducts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Faithful coefficient reflection to the integer group algebra proves U_t*V_t=A_t and V_t*U_t=A_(t-1). The diagonal identities are D_t*T_t=T_t and T_t*D_t=T_(t-1); both actual factor orders are retained.

**Definition 1.11 (The literal Type-valued chain at Nat.dist t r).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.prescribedChain`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.prescribedChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Descending steps use exactly (U_s,V_s); ascending steps use those same factors in swapped order. The recursive Chain retains each node and each factor equality. Its length is Nat.dist t r.

**Theorem 1.12 (The diagonal chain is the nil chain).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.prescribedSelf`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.prescribedSelf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At t=r the dependent chain is HEq to Chain.nil at the same A_t. This is a zero-step SSE chain; no minimum positive SE or certificate lag is identified with zero.

**Theorem 1.13 (The actual endpoint coefficient formula).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualAt_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualAt_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before truncation the coefficient is q^3*n+q*T(i,j)*(q*[g=1]-1). This formula keeps every group label and explains the coefficientwise natural reflection.

**Theorem 1.14 (Every endpoint coefficient is positive).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualAt_positive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualAt_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nontrivial H and n>=2, every coefficient of every actual A_t is positive. Inactive entries have q^3*n; active entries have q^3*n+q*(q-1) at the unit and q^3*n-q elsewhere. The strict lower estimate uses q>=2 and n>=2.

**Theorem 1.15 (Actual diagonal continuation).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualLoops`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualLoops` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>0, T(i,i)=0 and the unit coefficient on the diagonal is q^3*n>0. The proof selects the actual unit label and copy zero as a legal loop. No abstract independent continuation is substituted.

**Definition 1.16 (A rational nonunital homomorphism).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.rationalComplement`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.rationalComplement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The augmentation splitting identifies Q[H] with Q times its reduced component. Suppressing only the first component and transporting back gives the actual nonunital additive multiplicative map.

**Theorem 1.17 (The original complement formula).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.rationalComplement_apply`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.rationalComplement_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transported map is exactly x-rationalAugmentation(x)*average(H). This identifies the paper formula, rather than an unnamed quotient. It supplies the projection needed for the existing arbitrary rectangular barrier; this document does not claim that the full original barrier consumer has been completed.

Admission and audit: source-level classification is separate from Lean acceptance. The delivery packet records the per-declaration content and bind-only review, actual consumers, and any unfinished four-slot registration. No registration is claimed merely from this exposition or from a successful compiler run.

Remaining original25 obligations include padded partition coordinates, exact positive depths and actual inertness, arbitrary rectangular SSE and arbitrary positive SE lower bounds, full certificate counting/minima, the actual prescribed history map with signed windows, and all twisted counts for every h and every positive j. Earlier accepted transient alignment evidence does not close these obligations, and the failed final receiver is not used here.

Provenance and literature: these are repository constructions building on the existing counted-path, prescribed-array, positive-perturbation and augmentation-splitting suppliers. No external priority or literature novelty claim is made.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualAt`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualAt_coefficient`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualAt_positive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.actualLoops`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.concatEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.encoding`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.exact_fixed_cut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.factorPositive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.finite_overlap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.full_inverse_coherence`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.full_overlap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.prescribedChain`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.prescribedProducts`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.prescribedSelf`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.rationalComplement`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.rationalComplement_apply`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.run_path`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths](../CountedGroupChainPaths.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance](../FixedPositivePartitionSseDistance.md)
