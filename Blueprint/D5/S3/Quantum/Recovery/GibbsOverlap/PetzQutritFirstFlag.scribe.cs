using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.GibbsOverlap;

internal sealed class PetzQutritFirstFlagDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The certified qutrit deficit dominates the complementary-flag bound.",
        H("Strict two-flag overlap deficit"),
        Blocks(
            Paragraph(Text(
                "Use the integer Hermitian matrices A and B from the polar-overlap witness. "
                + "Put N = Re Tr exp(2B), Q = exp(2B)/N, ε = 2⁻¹⁰⁰, M = exp(2A), "
                + "D₁ = εM, and D₂ = I − εM. Both effects are positive definite, "
                + "their sum is I, and Q is a faithful density matrix.")),
            Entry("effects-sum", "effects_sum", "The two effects sum to the identity", "D₁ + D₂ = I."),
            Entry("qutrit-faithfulness", "Q_posDef", "The retained Gibbs state is faithful",
                "The matrix of Q is positive definite."),
            Entry("matrix-exponential", "mat_exp", "The matrix representation preserves the exponential",
                "For every qutrit CStarMatrix, the matrix of its exponential is the exponential of its matrix."),
            Entry("first-effect-faithfulness", "D1_strictlyPositive", "The first effect is strictly positive",
                "The exponential of 2A is strictly positive, as is its scale ε."),
            Entry("second-effect-faithfulness", "D2_strictlyPositive", "The complementary effect is strictly positive",
                "The bound εM ≤ I/2 gives D₂ ≥ I/2."),
            Entry("strict-overlap-deficit", "two_flag_overlap_lt_partition",
                "The sum of overlap norms is strictly below the partition trace",
                "For Ωᵢ = exp(log Q + log Dᵢ), the sum of ‖√Ωᵢ √Dᵢ √Q‖₁ is strictly below "
                + "the sum of Re Tr Ωᵢ. The first flag rescales the certified word "
                + "exp(A+B) exp(A) exp(B) by ε/N and has deficit less than −ε exp(18)/(2N). "
                + "The complementary-flag bound gives a deficit at most ε² exp(44)/2. "
                + "Since N ≤ 3 exp(32) and ε exp(44) < exp(−14)/3, the sum is strictly negative.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role = DescribeRole.Lemma) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
