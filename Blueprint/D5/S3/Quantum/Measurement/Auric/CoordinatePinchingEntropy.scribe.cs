using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class CoordinatePinchingEntropyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurement/Auric/CoordinatePinchingEntropy.";

    private static LibraryNoteRef EntropicIdentities =>
        LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entropy and complementary records of a coarse coordinate PVM on pure phase signals.",
        H("Coarse coordinate pinching of pure phase records"),
        Blocks(
            Paragraph(Text("Let c map the finite coordinate set to Fin k. The input for label j has vector ψⱼ(i) = tᵢ uⱼᵢ, with |uⱼᵢ| = 1 and Σᵢ tᵢ² = 1. Let P_b project onto the fiber of c at b and q_b = Σ_{c(i)=b} tᵢ². The actual unread channel applies Π(X) = Σ_b P_b X P_b. Entropies and logarithms use nats. The statements concern finite states, channels and readouts at a fixed measurement.")),
            Describe.Lean(DescribeId.Create("orthogonal-block-mixture"),
                DeclarationHandle.Create(Module + "pinchedPhaseStates_eq_mixture"),
                H("The pinched signal is an orthogonal mixture"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EntropicIdentities),
                Blocks(Paragraph(Text("Normalize each nonzero vector P_b ψⱼ by √q_b. Vectors from different blocks have disjoint coordinate support. The weighted projector onto each normalized vector reconstructs its unnormalized rank-one summand, and the masked vector vanishes for q_b = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pinching-entropy-gain"),
                DeclarationHandle.Create(Module + "phase_pinching_entropy_gain"),
                H("The entropy gain is H(q)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EntropicIdentities),
                Blocks(Paragraph(Text("Apply OrthogonalRecordEntropy.orthogonal_mixture_entropy to the normalized nonzero block states. Their entropies and the input entropy are zero. Restoring the zero-weight terms to the Shannon sum adds zero, including for empty fibers. Watrous Definition 5.17 and equations (5.82)–(5.84) give the spectral entropy convention."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-block-logarithm"),
                DeclarationHandle.Create(Module + "pinchedPhaseStates_log"),
                H("The logarithm on the positive-weight block states"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EntropicIdentities),
                Blocks(Paragraph(Text("The matrix logarithm is the sum of log(q_b) times the projectors onto the normalized nonzero block vectors. The finite-spectrum calculus uses Real.log 0 = 0 on the joint kernel. Watrous equation (1.145) gives the spectral functional calculus."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coarse-pinching-support"),
                DeclarationHandle.Create(Module + "phase_supportContained"),
                H("The coherent input is supported in the pinched signal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EntropicIdentities),
                Blocks(Paragraph(Text("A kernel vector has zero quadratic pairing with the pinched output. The pairing is a sum of squared overlaps with the masked vectors. Every overlap vanishes, so the kernel vector is orthogonal to their sum ψⱼ."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("support-aware-entropy-gain"),
                DeclarationHandle.Create(Module + "phase_pinching_relative_entropy"),
                H("The actual support-aware relative entropy also equals H(q)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EntropicIdentities),
                Blocks(Paragraph(Text("The support inclusion places the actual Umegaki divergence in its finite branch. Each P_b commutes with the logarithm of the output, so cyclicity of trace identifies its pairing with the input and with the pinched output. Watrous Definition 5.18 and equation (5.85) give the support convention and trace formula."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-record-marginals"),
                DeclarationHandle.Create(Module + "copiedPhaseState_marginals"),
                H("One recording isometry gives both actual marginals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EntropicIdentities),
                Blocks(Paragraph(Text("The coherent copy sends |i⟩ to |i⟩⊗|c(i)⟩. The joint blocks are P_b ρⱼ P_d. Tracing the flag gives the actual unread signal, and tracing the residual gives diag(q) for every label. Watrous equation (2.34) specifies the partial trace on product-basis entries."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("environment-holevo-zero"),
                DeclarationHandle.Create(Module + "copied_environment_holevo_zero"),
                H("The environment has zero Holevo label information"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EntropicIdentities),
                Blocks(Paragraph(Text("For every normalized prior the averaged environment state equals each individual environment state. Its entropy therefore equals the prior-weighted average entropy. Holevo, arXiv:quant-ph/9611023v1, sections 2–3, defines the entropy difference on p. 2 and displays it in equation (5) on p. 3."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("classical-flag-diagonal-readout"),
                DeclarationHandle.Create(Module + "classicalPhaseRecord_readout"),
                H("The residual coordinate PVM recovers the dephased flag"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Dephase the flag within the actual copied state. The joint probability of flag b and residual outcome d is q_b when b = d and zero otherwise."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("classical-flag-conditional-entropy"),
                DeclarationHandle.Create(Module + "classicalPhaseRecord_conditional_entropy"),
                H("The dephased flag has zero conditional entropy given the residual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the same pure-state coarse pinching entropy calculation on the product register. Its lifted block weights remain q, so the dephased joint state and its residual marginal both have entropy H(q)."))),
                DescribeRole.Theorem))));
}
