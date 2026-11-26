using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RobinActualWeightedTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedTail.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted response of the actual zero series.",
        H("Weighted response of the actual zero series"),
        Blocks(
            Paragraph(Text("The zero part of the integrated formula has a summable majorant from the norms of all actual coefficients. Dominated convergence exchanges the occurrence sum with the weighted integral.")),
            Describe.Lean(DescribeId.Create("mode-transport"), DeclarationHandle.Create(Prefix + "mode_transport_eq"),
                H("Integrated mode transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The boundary term minus the d-weighted integral of a single integrated mode equals its weighted zero contribution."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-zero-response"), DeclarationHandle.Create(Prefix + "zeroQ_response"),
                H("Actual spectral response"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real j at least 1 and every positive lower endpoint, the weighted response of the actual zero part is the sum of its occurrence contributions."))), DescribeRole.Theorem)
        )));
}
