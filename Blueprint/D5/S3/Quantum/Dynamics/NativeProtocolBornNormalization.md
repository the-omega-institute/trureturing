# Complete native protocols and arbitrary position cuts

## Abstract

Physical Born normalization for the complete original sixteen-bit protocol tree.

**Theorem 1.1 (The complete original tree has unit total mass and every acquired event has its actual cut trace).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), (\forall e: \operatorname{Function}\left(\operatorname{Path}\left(T\right), \operatorname{Bool}\left(\right)\right), (\forall I: \operatorname{Finset}\left(\operatorname{Fin}\left(16\right)\right), ((((\sum_{p \in \operatorname{Path}\left(T\right)} \sum_{z \in \operatorname{Basis}\left(\right)} \operatorname{mass}\left(T, p, z\right) = 1) \land ((0 \leq \operatorname{eventMass}\left(T, \operatorname{historyEvent}\left(e\right)\right)) \land (\operatorname{eventMass}\left(T, \operatorname{historyEvent}\left(e\right)\right) \leq 1))) \land \operatorname{PosSemidef}\left(\operatorname{eventCut}\left(T, I, e\right)\right)) \land (\operatorname{trace}\left(\operatorname{eventCut}\left(T, I, e\right)\right) = \operatorname{complex}\left(\operatorname{eventMass}\left(T, \operatorname{historyEvent}\left(e\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization.original_complete_born_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Giacomo M. D'Ariano; Paolo Perinotti (2009). *Theoretical framework for quantum networks*. DOI: [10.1103/PhysRevA.80.022339](https://doi.org/10.1103/PhysRevA.80.022339). URL: <https://arxiv.org/abs/0904.4483v2>.

*Commentary.*

The objects are the original NativeProtocolGraft.Tree, Basis, omega0, gate, callMatrix, projector, Path and mass. Basis consists of all sixteen-bit words at the shifted original positions. The unique fixed root has ones at positions 0, 4 and 8. The proof uses the full matrices at every address in Fin 14, rather than a two-dimensional model supplied as an additional premise.

On each active center-bit pair the actual gate coefficients are a,b,c from the existing calibration calculation. Their existing squared norms, the golden quadratic identity and the actual phase norm give orthogonal unit rows. The remaining control blocks are zero or identity before the phase gate. Reindexing the full carrier by the center-bit involution proves exact energy conservation. Forward calls use this identity and inverse syntax uses nine iterations of the same actual matrix. The original resource counter still charges nine calls; no semantic equality with a separately defined matrix inverse is asserted.

The sum of all terminal squared amplitudes is conserved for every incoming full-carrier vector. Its proof recurses over the original finite tree. Each gate preserves energy, and each selector projector keeps precisely one outcome for every basis word, so the complete outcome sum preserves energy exactly. Each child can have its own feedback addresses, depth and stopping label. Unused outcomes, zero vectors, refusals, failures and early stops remain in the original Path type and its sum. No total-probability, gate-unitarity or projector-completeness certificate is an input.

Applying that conservation to the original normalized computational root gives unit total Born mass, including every final computational result. An acquired event is a Boolean function of the original prefix path, independent of any future report. The existing original_event_cut_mass_and_psd theorem supplies the same acquired event's b1 marginal and exact real trace. Its positive semidefinite matrix has nonnegative trace, giving the zero lower bound; domination by the complete Born sum gives the upper bound one. Any declared complete prefix is itself such a Tree; the theorem therefore applies at that same common cut.

For any subset I of the sixteen positions, including the empty and full subsets, splitAt is the pinned equivalence restricting a word to I and its complement. The row and complement bases are Boolean functions on those two actual position subtypes. Their dimensions are two to the cardinality of I and two to the cardinality of its complement. cutReduced is the existing right partial trace of the outer product of the same actual branch vector after this coordinate equivalence. eventCut sums those matrices over exactly the acquired histories. The existing partial-trace positivity and trace theorems supply positive semidefiniteness and equality of its complex trace with the real event mass. This reduction is a mathematical marginal and adds no physical record deletion, new register or coherent sum of distinct histories.

This is a partial consequence of V88 definitions 23.1 and 23.2 and the physical trace premise used in theorem 24.1. The same-cut integer-coordinate and signed-embedding theorem below supplies the determinant descent; the determinant resource lower bound, both minimum-eigenvalue lower bounds, faithful-cut existence and the five-call reference-history and full-record Petz compiler remain separate obligations. The arithmetic lower bound for a positive raw event remains the existing original_event_resource_bounds result. The full source atom remains open and uncovered.

**Theorem 1.2 (Quadratic integer coordinates and the exact signed embedding of the same cut).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), (\forall e: \operatorname{Function}\left(\operatorname{Path}\left(T\right), \operatorname{Bool}\left(\right)\right), (\forall I: \operatorname{Finset}\left(\operatorname{Fin}\left(16\right)\right), ((((\operatorname{trace}\left(\operatorname{eventCut}\left(T, I, e\right)\right) = \operatorname{complex}\left(\operatorname{eventMass}\left(T, \operatorname{historyEvent}\left(e\right)\right)\right)) \land (\operatorname{det}\left(\operatorname{eventCut}\left(T, I, e\right)\right) = \operatorname{complex}\left(\operatorname{realPhysical}\left(\operatorname{cutDetCoordinates}\left(T, I, e\right)\right)\right))) \land (\operatorname{det}\left(\operatorname{conjugateEventCut}\left(T, I, e\right)\right) = \operatorname{complex}\left(\operatorname{realConjugate}\left(\operatorname{cutDetCoordinates}\left(T, I, e\right)\right)\right))) \land (\forall i: \operatorname{CutBasis}\left(I\right), (\forall j: \operatorname{CutBasis}\left(I\right), (\operatorname{Apply}\left(\operatorname{conjugateEventCut}\left(T, I, e\right), i, j\right) = \sum_{p \in \operatorname{Path}\left(T\right)} \sum_{z \in \operatorname{CutRest}\left(I\right)} \operatorname{if}\left(\operatorname{Apply}\left(e, p\right), {{-1}}^{\operatorname{restExponent}\left(I, z\right)+\operatorname{rowExponent}\left(I, j\right)}*\operatorname{conjugateAmplitude}\left(\operatorname{branch}\left(T, p, \operatorname{initial}\left(\right)\right), \operatorname{splitAtInverse}\left(I, i, z\right)\right)*\operatorname{star}\left(\operatorname{conjugateAmplitude}\left(\operatorname{branch}\left(T, p, \operatorname{initial}\left(\right)\right), \operatorname{splitAtInverse}\left(I, j, z\right)\right)\right), 0\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization.original_event_cut_integer_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian Stewart and David Tall (2025). *Algebraic Number Theory and Fermat's Last Theorem*. DOI: [10.1201/9781003462002](https://doi.org/10.1201/9781003462002).

*Commentary.*

The theorem quantifies over the unchanged original tree, its acquired-path event and any subset I of the sixteen positions. The same eventCut supplies both the complex trace and the determinant. No positivity, covariance, gate-unitarity or normalization certificate is assumed. The statement includes zero events, singular cuts, and empty and full subsets; it makes no full-rank inference.

Let r(i) be the retained word's Hamming parity as zero or one. Let s(z) be the complementary word's parity relative to the fixed original root. Restriction along splitAt proves that the original relative exponent is r(i) plus s(z), modulo two. In the inverse-golden integer ring tau times (tau plus one) equals one. Multiplying the computed coefficient by tau plus one to the power r(i)s(z) therefore extracts the physical factors beta to r(i) and beta to s(z) without leaving the four-integer coefficient ring. The histories and the complementary word are unchanged.

cutKernel is the sum over exactly the selected original histories and complementary words of tau to s(z) times the extracted coefficient at i times the coefficient conjugate at j. This conjugation fixes the inverse-golden base ring and sends eta to minus tau minus eta. The original eventCut is the physical evaluation of this kernel multiplied on both sides by the diagonal beta to r(i). The kernel equals its coefficient conjugate transpose, so its determinant is fixed by that conjugation. In the two explicit integer coordinates this forces its eta coefficient to vanish. Multiplying its surviving inverse-golden pair by the product of tau to r(i) gives cutDetCoordinates, an actually computed element of O, with the physical determinant as its realPhysical evaluation.

conjugateEventCut applies the nonphysical homomorphism to this exact same kernel and uses the nonphysical beta on both sides. Its determinant is realConjugate of the same cutDetCoordinates. Since the nonphysical beta is imaginary, this embedded matrix equals the sum of embedded branch outer products with sign minus one to s(z) plus r(j). Equivalently it is A C A adjoint J, with complement sign C and row-parity sign J. Replacing this expression by an unsigned positive Gram matrix would change the nonphysical determinant. Coefficient conjugation is proved compatible with both S evaluations; conjugation of the square-root factor supplies the displayed sign.

These are the same-cut arithmetic descent and embedding identities used in V88 theorem 24.1, equations 24.7, 24.9 and 24.10. They do not yet prove the nonphysical determinant norm estimate, the determinant resource lower bound or either eigenvalue bound. Positive event mass already has its original_event_resource_bounds lower bound and is not being re-proved. Faithfulness still requires full rank of this same eventCut. The whole atom remains open and uncovered. The four-slot source reconstruction audit remains unfinished under issue 26627.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization.original_complete_born_law`
- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization.original_event_cut_integer_coordinates`
- Dependency: [D5/S3/Quantum/Dynamics/NativeProtocolCalibration](NativeProtocolCalibration.md)
