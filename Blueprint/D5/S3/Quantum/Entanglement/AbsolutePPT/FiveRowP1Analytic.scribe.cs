using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class FiveRowP1AnalyticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The analytic equality neighborhood of the scalar system.",
        H("FiveRowP1Analytic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fiverowp1analytic-analytic-region"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Analytic.analytic_region"),
                H("Full analytic equality neighbourhood"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 25 <= N <= 90, every real 10 <= j <= N-15, r <= 1/10 and D <= 1/4, the scalar hypotheses imply a nonnegative energy gap. Splitting at H=2-r-D/5 combines concavity below that value with the cap and increasing gap above it, including the equality boundary r=D=0."))), DescribeRole.Theorem))));
}
