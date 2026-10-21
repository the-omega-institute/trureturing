using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal;

internal sealed class N25APart04Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact structural traversal and local numerical premises of the same full scalar reduction.",
        H("Exact P1 forest N25APart04"),
        Blocks(
            Describe.Lean(DescribeId.Create("traversal-334"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart04.traversal_334"),
                H("Exact forest premise traversal_334"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact rational or structural premise is used in the complete forest check, which supplies the continuous real scalar inequality."))),
                DescribeRole.Theorem))));
}
