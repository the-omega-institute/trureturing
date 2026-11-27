using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanShellScaleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Analytic/NymanShellScale";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Möbius shell sums at adjacent reciprocal scales",
        H("Möbius shell sums at adjacent reciprocal scales"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scale-difference"),
                DeclarationHandle.Create(Owner + ".scale_difference"),
                H("Uniform estimate between integer samples"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose W vanishes outside (1, 2) and has Lipschitz constant K. For 1/(N+1) ≤ t ≤ 1/N and N ≥ 1, the two scaled sums differ by at most 10K. Truncating both sums at 2(N+1) bounds the number of terms, and each term changes by at most 2K/N."))),
                DescribeRole.Theorem))));
}
