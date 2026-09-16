using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class NestedGridEntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/NestedGridEntropy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A legal binary refinement history imposes an entropy budget beyond the static averaging lower bound.",
        H("Nested Grid Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nested-grid-finite-entropy-budget"),
                DeclarationHandle.Create(Prefix + "binary_refinement_entropy_budget"),
                H("Finite resolution cost with explicit refinement losses"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The initial cell list is [1]. At each step an actual listed parent a+b is replaced by two positive children a and b, leaving the other cells unchanged. From these identities the proof derives positive unit total mass at every stage, the exact entropy increment, and a terminal entropy lower bound from the maximal-cell cap. Each nonnegative loss equals the cost of splitting below the cap plus the binary-entropy deficit of the split ratio. The theorem bounds final log resolution plus cumulative loss by log(2) times the sum of past caps. The ordinary consumer gives the sharp 1/log(2)^2 sequential error factor for the previously derived two-moment grid loss using the classical Niederreiter logarithmic construction. The sequence theorem and the full grid identification are not claimed as kernel-checked by this declaration."))),
                DescribeRole.Theorem))));
}
