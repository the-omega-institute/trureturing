using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.GronwallAbundant;

internal sealed class AsymptoticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-deletion constraints, missing-prime mass and finite-code entropy for proper GA1 integers.",
        H("Asymptotic"),
        Blocks(
            Describe.Lean(DescribeId.Create("codecost"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Asymptotic.codeCost"), H("The logarithmic cost of the three integer-code coordinates."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The logarithmic cost of the three integer-code coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("code-cost-eventually"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Asymptotic.code_cost_eventually"), H("The complete integer-code cost retains a uniform exponential saving."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete integer-code cost retains a uniform exponential saving."))), DescribeRole.Theorem))));
}
