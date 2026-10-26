using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data;

internal sealed class N55BDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact numerical premises for the original full continuous P1 scalar reduction.",
        H("Exact P1 forest N55B"),
        Blocks(
            Describe.Lean(DescribeId.Create("nodes"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N55B.nodes"),
                H("Ordered literal forest nodes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The ordered records retain every box endpoint, rule, child index and rational coefficient. These data assert no successful check."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("accepted"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N55B.accepted"),
                H("Exact forest premise accepted"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact rational or structural premise is used in the complete forest check, which supplies the continuous real scalar inequality."))),
                DescribeRole.Theorem))));
}
