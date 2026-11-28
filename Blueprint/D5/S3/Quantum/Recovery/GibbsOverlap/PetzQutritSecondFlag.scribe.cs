using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.GibbsOverlap;

internal sealed class PetzQutritSecondFlagDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritSecondFlag.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quadratic bound for the complementary effect in the Petz and Gibbs overlap.",
        H("Complementary-flag overlap bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("logarithm-under-matrix-representation"),
                DeclarationHandle.Create(Module + "mat_log"),
                H("The matrix representation preserves the logarithm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a self-adjoint CStarMatrix on a finite index type, mapping its spectral "
                    + "logarithm to the ordinary matrix representation gives the spectral logarithm "
                    + "of the represented matrix."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("quadratic-complementary-deficit"),
                DeclarationHandle.Create(Module + "second_flag_traceNorm_sub_le"),
                H("The complementary flag contributes at most a quadratic deficit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let Q be a faithful density matrix on a finite index type and suppose "
                    + "0 ≤ εM ≤ I/2. Set D = I − εM and Ω = exp(log Q + log D). Then "
                    + "‖√Ω √D √Q‖₁ − Re Tr Ω ≤ ε² Re Tr(Q M²)/2. "
                    + "Hilbert–Schmidt Hölder and the arithmetic–geometric mean inequality bound "
                    + "the deficit by (Re Tr(DQ) − Re Tr Ω)/2. The Gibbs variational identity and "
                    + "nonnegative relative entropy give Re Tr Ω ≥ 1 + Re Tr(Q log D). "
                    + "Functional calculus lifts log(1 − x) ≥ −x − x² on [0, 1/2] to D."))),
                DescribeRole.Theorem))));
}
