using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class CoordinatePinchingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurement/Auric/CoordinatePinching.";

    private static LibraryNoteRef DetectorDual =>
        LibraryNoteRef.Create("D5/L/Entropy/eldar2003detectors");

    private static LibraryNoteRef EldarForney =>
        LibraryNoteRef.Create("D5/L/Entropy/eldarforney2001quantumdetection");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first coordinate PVM determines the sharp success bound for flat phase records through every actual flagged continuation.",
        H("Exact decoding after a first coordinate PVM"),
        Blocks(
            Paragraph(Text("Use the same nonempty finite index set I of size N for labels j and coordinates i. The prior is uniform, 1/N. The complex phase entries satisfy |uⱼᵢ| = 1 and Σⱼ uⱼᵢ overline(uⱼₗ) = N δᵢₗ. The real profile t satisfies tᵢ ≥ 0 and Σᵢ tᵢ² = 1. The label state is ρⱼ = |ψⱼ⟩⟨ψⱼ| with ψⱼ(i) = tᵢ uⱼᵢ. All traces in the success statistic use their real parts.")),
            Paragraph(Text("A map c from I to Fin k specifies the first complete PVM. The projector P_b is diagonal with entry 1 at i exactly when c(i) = b. The masked profile s_b agrees with t on that fiber and is zero elsewhere. Write A_b = Σᵢ s_b(i). Unused outcomes and zero amplitudes are allowed. The unread Lüders action is Π(X) = Σ_b P_b X P_b, the repository's Conditioning.unreadState. The finite Kraus channel built from the same projectors applies this action to the density states.")),
            Describe.Lean(DescribeId.Create("pinched-phase-optimum"),
                DeclarationHandle.Create(Module + "isGreatest_pinchedPhase"),
                H("Exact optimum of the pinched ensemble"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(DetectorDual, EldarForney),
                Blocks(
                    Paragraph(Text("Among all I-labelled POVMs on the residual register, the greatest success is Σ_b A_b²/N. Pinching sends ρⱼ to the sum of rank-one matrices of the masked vectors s_b(i)uⱼᵢ. These vectors are kept with their original amplitudes, so each block contributes its original probability weight, including zero weight.")),
                    Paragraph(Text("For each block, the diagonal matrix D_b with i-th entry A_b s_b(i) dominates every masked rank-one matrix by JointRecordDecoding.diagonal_sub_rankOne_posSemidef. Thus X = (Σ_b D_b)/N is feasible for the finite discrimination dual. Pairing the positive slack with each positive effect, then summing using POVM completeness, bounds the score by Tr X = Σ_b A_b²/N. The finite dual and its slack conditions come from Eldar, Megretski and Verghese, IEEE Transactions on Information Theory 49(4), 1007–1012 (2003), arXiv:quant-ph/0205178, Section 3, Eqs. (14)–(20).")),
                    Paragraph(Text("Let vⱼ(i) = uⱼᵢ/√N and Fⱼ = |vⱼ⟩⟨vⱼ|. Column orthogonality gives Σⱼ Fⱼ = I by JointRecordDecoding.sum_phaseEffect. The overlap of vⱼ with the masked vector is A_b/√N, so this POVM attains the bound. Eldar and Forney, IEEE Transactions on Information Theory 47(3), 858–872 (2001), arXiv:quant-ph/0005132, Theorem 4, give the square-root readout for geometrically uniform pure ensembles. Here the explicit trace calculation covers arbitrary flat column-orthogonal phase matrices and profiles with zero entries."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("compressed-phase-attainment"),
                DeclarationHandle.Create(Module + "compressed_phaseEffect_attains"),
                H("Block-compressed effects also attain the optimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The compressed effects Π(Fⱼ) are positive and sum to the identity. Cyclicity of trace gives Tr(Π(M)X) = Tr(MΠ(X)) and Conditioning.unreadState_idempotent gives Π² = Π. Therefore the compressed and full effects have the same score on the pinched ensemble."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cross-block-decoding-loss"),
                DeclarationHandle.Create(Module + "phase_decoding_loss"),
                H("The loss is the sum of the cross-block amplitude products"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EldarForney),
                Blocks(
                    Paragraph(Text("JointRecordDecoding.pGuess_phase gives coherent success (Σᵢ tᵢ)²/N. Subtracting the pinched optimum gives (2/N) Σ_{b<d} A_b A_d. The order on Fin k counts each unordered pair of distinct blocks once."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinate-pinching-no-loss"),
                DeclarationHandle.Create(Module + "phase_decoding_no_loss_iff"),
                H("Equality holds exactly for single-block support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("All block masses are nonnegative and normalization forces at least one to be positive. The loss vanishes exactly when every other block has zero mass, equivalently when every nonzero amplitude belongs to a single fiber of c. Any two blocks containing positive amplitudes force a strict loss."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("terminal-channel-factors-through-pinching"),
                DeclarationHandle.Create(Module + "flaggedChannel_pinching"),
                H("The actual terminal channel factors through unread root measurement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This identity holds for every complete root PVM with identity root unitary, every same-register ProjectiveTree.Protocol continuation, and every input matrix X. The root PVM here need not be diagonal. A terminal history beginning with b has actual flagged Kraus matrix K_h satisfying K_h P_b = K_h, by ProjectiveTree.terminal_has_group_right_support for the singleton outcome followed by flag embedding. Its adjoint has left support P_b. Orthogonality kills the other root blocks in K_h Π(X) K_h†, leaving K_h X K_h†. Summing over the actual terminal histories gives Φ_q(Π(X)) = Φ_q(X) for the repository's recorded ProjectiveTree.flaggedChannel. The flag is a deterministic two-valued label of a fine history."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("flagged-identity-attainment"),
                DeclarationHandle.Create(Module + "flagged_identity_attains"),
                H("Identity leaves attain the bound with any terminal flag assignment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The joint effects act as Fⱼ in each flag block, so the measurement ignores the flag. With identity unitary at every leaf, the actual terminal Kraus for outcome b is P_b embedded in its assigned flag block. Pulling a joint effect back through these Kraus matrices gives Σ_b P_b Fⱼ P_b = Π(Fⱼ). Trace cyclicity transfers this score on the input states to the full effects Fⱼ on the pinched states. The calculation works when every leaf is assigned the same flag."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sharp-flagged-phase-optimum"),
                DeclarationHandle.Create(Module + "isGreatest_flaggedPhase"),
                H("Sharp success bound over all actual continuations and joint readouts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(DetectorDual),
                Blocks(
                    Paragraph(Text("Fix the first coordinate PVM and identity root unitary. Vary every descendant protocol and all I-labelled joint POVMs on Fin 2 × I, with positive effects that sum to the identity. For each such POVM, pull each effect Mⱼ back as Σ_h K_h† Mⱼ K_h. ProjectiveTree.flagged_normalized gives completeness, conjugation preserves positivity, and trace cyclicity preserves each pairing. Channel factorization allows the pullback to be scored on the pinched ensemble, whose exact optimum bounds the score. The common-flag identity leaves give an admissible maximizer.")),
                    Paragraph(Text("The operational result is the exact penalty imposed by this specified first observation even when the actual AURIC continuation and joint terminal readout are both unrestricted within the model. The bound accounts for the flag through the real terminal Kraus operators and the identity-leaf calculation makes it sharp. The finite discrimination dual and the coherent readout supply the underlying static estimates. The model is finite and stays on the same residual register throughout the tree."))),
                DescribeRole.Theorem))));
}
