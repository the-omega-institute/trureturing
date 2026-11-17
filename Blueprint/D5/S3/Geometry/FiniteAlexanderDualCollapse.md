# Finite Alexander dual collapse

## Abstract

Fixed labeled complements reverse free pairs and compute a one-critical-face cell attachment.

**Definition 1.1 (A fixed labeled ground).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Supported`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.Supported` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Supported W K means that every nonempty K-face is a subset of W. The ambient finite type stays unchanged and may include ghost labels.

**Definition 1.2 (Augmented properness).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Proper`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Proper W K means that W is not an augmented K-face. AugmentedFace always includes the empty face, so this hypothesis is false for empty W and excludes the void-dual ambiguity.

**Definition 1.3 (Native fixed-ground dual faces).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nonempty faces s of the dual are exactly those with s contained in W and W minus s absent from the augmented primal. Outside the proper primal domain this native object is only the nonempty skeleton; augmenting it does not encode a void dual.

**Theorem 1.4 (The proper-domain augmented bridge).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual_augmented`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual_augmented` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite W, native complex K with W absent from its augmented faces, and finite s, s is an augmented dual face if and only if s is contained in W and W minus s is not an augmented K-face. This includes the empty face and faces using labels outside W.

**Theorem 1.5 (Duality reverses containment).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If K is a subcomplex of L on the same ambient labels, then the native dual of L on W is a subcomplex of the native dual of K on W. Augmented use of this containment retains the proper-domain bridge.

**Theorem 1.6 (Double dual on the supported proper domain).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a native complex K supported on W and with W absent from its augmented face family, taking the fixed-W dual twice gives exactly K as a complex on the original labels. Neither vertices nor ghost labels are removed.

**Definition 1.7 (Constructing the reverse complementary pair).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reversePair`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.reversePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let a primal elementary pair have ambient contained in a fixed supported proper D. Its dual lower face is W minus the primal upper face; its apex is the same label, and its upper is W minus the primal lower. The primal upper is a D-face, so properness proves the new lower is nonempty. Freeness follows because any dual coface has complement a primal subface of the old upper, and the only deleted such faces are the old pair.

**Theorem 1.8 (The exact reverse endpoint).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reversePair_retained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.reversePair_retained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such supported proper D and primal pair contained in D, the retained complex of the constructed reverse pair is literally the fixed-W dual of the primal ambient. Its ambient is the fixed-W dual of the primal retained complex.

**Definition 1.9 (Source and output pair relation).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.ReversePairSpec`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.ReversePairSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The relation takes the source pair first and the output pair second. It records both native endpoint equalities, the complement lower and upper, the unchanged apex, the nonempty lower, upper cardinality one above lower, lower cardinality equal to W cardinality minus primal upper cardinality, and both exact augmented proper-domain membership formulas.

**Definition 1.10 (Finite sequence reversal).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reverseSequence`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.reverseSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original Sequence owner is reused. Recursion reverses the tail and appends the constructed reverse pair, so an actual finite primal sequence K to L returns actual owner data for the dual L to the dual K. No collapse or topological map is assumed as an output field.

**Theorem 1.11 (Every ordered pair is retained).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reverseSequence_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.reverseSequence_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any primal Sequence K L with K contained in a supported proper D, the constructed output pair list and the reversed primal list satisfy Forall2 with the source-first relation explicitly applied to the second and first list arguments. All complement labels, endpoints, cardinalities and augmented laws are retained at each step.

**Theorem 1.12 (Every intermediate frame is retained).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reverseSequence_frames`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.reverseSequence_frames` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses the complete frame list of the constructed reverse sequence equals the original frame list reversed and mapped by the fixed-W dual. Both endpoints are included; no default frame or finite-type resizing occurs.

**Definition 1.13 (Extension over a retained subcomplex cone).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.extendOverRetainedCone`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.extendOverRetainedCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an owner Sequence K L, a subcomplex B of L and a label a fresh in K, the construction returns a Sequence from K union cone(a,B) to L union cone(a,B). The original owner pair extension proves that no cone face can contain a removed lower face.

**Definition 1.14 (Deleting one maximal face).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.removeMax`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.removeMax` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The faces are exactly Q-faces other than sigma. The maximality condition says any Q-face containing sigma equals sigma; it is what makes this deletion downward closed. This deletion is separate from an elementary collapse.

**Theorem 1.15 (The augmented maximal-face deletion).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.removeMax_augmented`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.removeMax_augmented` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty sigma satisfying the maximality condition, an augmented face of the deletion is exactly an augmented Q-face different from sigma. In particular the empty augmented face survives. Membership of sigma in Q is a separate hypothesis of the critical-face identities.

**Definition 1.16 (The full complementary simplex).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.simplex`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.simplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native simplex on lambda has every nonempty subset of lambda as a face, with its augmented empty face supplied by the existing AugmentedFace convention.

**Definition 1.17 (The whole complementary boundary).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.boundary`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native boundary has every nonempty proper subset of lambda. For nonempty lambda its augmented faces are all proper subsets, including the empty face. A singleton lambda has empty ordinary boundary and augmented boundary consisting of the empty face.

**Theorem 1.18 (The critical complementary simplex).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.critical_dual_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.critical_dual_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If nonempty sigma is a maximal Q-face and Q is supported on W, the fixed-W dual after deleting sigma equals the old dual union the full simplex on W minus sigma. For a proper subface of the complementary simplex, the primal complement strictly contains sigma and is excluded by maximality.

**Theorem 1.19 (Exactly the boundary meets the old dual).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.critical_dual_intersection`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.critical_dual_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under those hypotheses the old dual intersected with the full simplex on W minus sigma equals its entire native boundary. The whole complementary face is absent from the old dual because its primal complement is sigma itself.

**Definition 1.20 (Computing the finite dual table).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dualTable`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.dualTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a finite augmented primal face table, filter the powerset of W by absence of the exact W complement. No ambient label is deleted. FiniteDualData carries the total equivalence with the native augmented dual on the proper domain.

**Definition 1.21 (Exact finite output and native bridge).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.FiniteDualData`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.FiniteDualData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This output consists of a finite face table and a proof, for every finite s, that table membership is equivalent to AugmentedFace of the native dual. Properness is an explicit parameter. The output also reconstructs the original native primal by double duality whenever its ground support is supplied.

**Definition 1.22 (Finite one-critical-face input).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Certificate`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.Certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input gives W; native D, E and Q with exact finite augmented face tables; support and augmented properness of D; a specified owner Sequence D Q; a nonempty maximal Q-face sigma outside E; a specified owner Sequence from Q minus sigma to E; and an apex a outside W. No desired dual collapse, retraction, contraction, null attaching map or sphere equivalence is an input.

**Definition 1.23 (Critical-face deletion).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Qprime`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.Qprime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Qprime is the existing removeMax of the original Q at sigma with its supplied maximality proof; this is separate from the ordinary collapse-pair list.

**Definition 1.24 (Original complementary labels).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.lambda`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.lambda` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

lambda is exactly W minus sigma on the unchanged original ambient label type.

**Definition 1.25 (Complementary sphere dimension).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.d`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.d` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

d is the natural number lambda.card minus one. The arithmetic theorem separately proves the nonempty complementary-face and exact dimension equations.

**Definition 1.26 (Original D dual).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Dstar`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.Dstar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Dstar is exactly dual W D with the original fixed ground W.

**Definition 1.27 (Original E dual).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Estar`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.Estar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Estar is exactly dual W E with the original fixed ground W.

**Definition 1.28 (Original Q dual).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Qstar`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.Qstar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Qstar is exactly dual W Q with the original fixed ground W.

**Definition 1.29 (Critical deletion dual).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.QprimeStar`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.QprimeStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

QprimeStar is exactly dual W Qprime with the same W and the actual critical-face deletion.

**Definition 1.30 (Original-apex cone).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.C`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C is exactly cone a Dstar using the original supplied apex label a outside W.

**Definition 1.31 (Original ambient K).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.K`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K is exactly Estar union C on the original labels; it is the ambient of the computed relative reduction.

**Definition 1.32 (Retained cell attachment).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.X`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.X` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

X is exactly QprimeStar union C. Its one-cell decomposition and whole-boundary intersection are proved by the separate source theorems.

**Definition 1.33 (Standalone contractible core).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.P`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P is exactly Qstar union C. Its collapse and contraction are constructed on P alone; no freeness across X is asserted.

**Definition 1.34 (Actual critical-deletion face table).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.QprimeFaces`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.QprimeFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

QprimeFaces is the finite table Qfaces.erase sigma. It is a public def, not a theorem; the private exactness proof is used by dualData.

**Theorem 1.35 (Nondegenerate complementary dimension).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.arithmetic`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every certificate, lambda equals W minus sigma and is nonempty, disjoint from sigma, with their union exactly W. The cardinality of W is the sum of their cardinalities and is at least two. With d equal to lambda cardinality minus one, d plus one equals lambda cardinality and d equals W cardinality minus sigma cardinality minus one. Thus empty and singleton W cannot support this input.

**Definition 1.36 (Finite computed dual memberships).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dualData`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.dualData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four returned finite tables give the exact augmented faces of D dual, E dual, Q dual and the dual after the critical deletion. The critical primal table is computed by erasing sigma from the exact Q table. All four properness proofs follow from the prescribed primal sequences and D properness.

**Definition 1.37 (The first dual reduction).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.firstDual`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.firstDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reversing the second primal sequence produces an actual owner Sequence from E dual to the dual of Q minus sigma. Since D dual is retained, its literal coordinate inclusion is fixed by the realized relative deformation.

**Definition 1.38 (The independent second dual sequence).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.secondDual`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.secondDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reversing the first primal sequence produces an actual owner Sequence from Q dual to D dual. It supplies a collapse only on its stated ambient complex.

**Definition 1.39 (The actual cone-relative reduction).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reduction`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.reduction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Put C equal to cone(a,D dual), K equal to E dual union C, and X equal to the dual of Q minus sigma union C. Extending the first dual sequence over this retained cone computes K collapsing to X.

**Definition 1.40 (The separate collapse of P).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.collapseP`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.collapseP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Put P equal to Q dual union C. The existing owner extension computes P collapsing to C, fixing all of C. This collapse is on P alone; adjoining the complementary disk may create new cofaces that obstruct its pairs in X.

**Definition 1.41 (The unchanged attaching inclusion).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.j`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.j` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map j from the actual realization of D dual to the actual realization of E dual is the existing subcomplex inclusion, with every coordinate unchanged. It is never replaced by a zero or null map.

**Definition 1.42 (Actual relative retraction onto X).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reductionSDR`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.reductionSDR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sequence.realize produces the coordinate retraction from K to X, its retraction-inclusion identity, and a homotopy relative to the entire realization of X. The maps are computed from the finite sequence.

**Definition 1.43 (Actual retraction from P to C).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.pSDR`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.pSDR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sequence.realize applied to the separate P collapse produces the coordinate retraction to C and the homotopy fixing every point of C.

**Definition 1.44 (The computed contraction of P relative to the apex).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.pContraction`

*Formalization.* `D5/S3/Geometry/FiniteAlexanderDualCollapse.pContraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing owner concatenates the finite relative retraction to C with its actual linear cone contraction to the coordinate apex a. The result is a HomotopyRel from the identity on P to the constant actual apex map, fixed on the singleton containing the actual included apex. No extension of this contraction across the attached disk is asserted.

**Theorem 1.45 (The pointwise fixed-apex law).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.pContraction_fixed_apex`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.pContraction_fixed_apex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit-interval time, the actual pContraction sends the included cone apex to itself. The proof is the singleton relative property of the same composed SDR and cone contraction; it does not introduce a desired contraction field or a second homotopy.

**Theorem 1.46 (The exact one-cell union).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.cell_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.cell_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every certificate the actual reduced complex X is exactly P union the full lambda simplex on the original labels. This follows from the critical dual identity and the union with the same actual cone.

**Theorem 1.47 (The full boundary and the small case).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.cell_intersection`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.cell_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every certificate, P intersected with the full lambda simplex is exactly the lambda boundary. For every finite s, an augmented face of that boundary is exactly a proper subset of lambda. If lambda has cardinality one, the native boundary is bottom; augmenting this bottom gives the empty face, not a void face family. The cone creates no extra overlap because its apex is outside W and D dual is contained in Q dual.

**Theorem 1.48 (An actual face of E dual).**

Lean statement: `D5/S3/Geometry/FiniteAlexanderDualCollapse.complementary_face`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAlexanderDualCollapse.complementary_face` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complementary lambda is a nonempty E-dual face. Its complement is the original nonempty sigma, which was explicitly absent from E. E dual therefore has an ordinary point even when D dual or Q dual has empty ordinary realization.

## References

- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.C`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Certificate`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Dstar`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Estar`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.FiniteDualData`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.K`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.P`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Proper`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Qprime`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.QprimeFaces`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.QprimeStar`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Qstar`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.ReversePairSpec`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.Supported`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.X`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.arithmetic`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.boundary`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.cell_decomposition`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.cell_intersection`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.collapseP`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.complementary_face`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.critical_dual_intersection`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.critical_dual_union`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.d`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dualData`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dualTable`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual_antitone`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual_augmented`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.dual_involutive`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.extendOverRetainedCone`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.firstDual`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.j`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.lambda`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.pContraction`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.pContraction_fixed_apex`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.pSDR`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reduction`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reductionSDR`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.removeMax`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.removeMax_augmented`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reversePair`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reversePair_retained`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reverseSequence`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reverseSequence_frames`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.reverseSequence_pairs`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.secondDual`
- Truth anchor: `D5/S3/Geometry/FiniteAlexanderDualCollapse.simplex`
- Dependency: [D5/S3/Geometry/FiniteRelativeSimplicialCollapse](FiniteRelativeSimplicialCollapse.md)
