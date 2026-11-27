using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanFixedRationalKernelLipschitzDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Analytic/NymanFixedRationalKernelLipschitz";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lipschitz bound for the rational cubic kernel",
        H("Lipschitz bound for the rational cubic kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("b-lipschitz"),
                DeclarationHandle.Create(Owner + ".b_lipschitz"),
                H("A global Lipschitz constant"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each truncated cubic is Lipschitz on [1, 2] by the difference-of-cubes identity. Clamping to that interval preserves the kernel value and extends the estimate to every pair of real inputs."))),
                DescribeRole.Theorem))));
}
