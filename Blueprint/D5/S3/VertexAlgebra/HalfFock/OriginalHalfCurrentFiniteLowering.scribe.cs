using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;

internal sealed class OriginalHalfCurrentFiniteLoweringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering.";

    private static DocumentBlock Result(string id, string declaration, string heading, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite evaluation of the original lowering action on marked oscillator words",
        H("Finite Half-Current Lowering"),
        Blocks(
            Result("half-current-evaluate-lowering-word", "evaluate_lowering_word",
                "Termination at the original cutoff",
                "The normally ordered polynomial evaluates to the factorial-normalized original "
                + "lowering flow at every cutoff for which the remaining powers vanish."),
            Result("half-current-evaluate-word-step", "evaluate_word_step",
                "Finite creation and pair contraction",
                "An unpaired oscillator contributes the finite binomial creator. A paired "
                + "oscillator contributes the original Gram entry times the ordinary coefficient "
                + "of the regular Cauchy correction."))));
}
