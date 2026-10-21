using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal;

internal sealed class N25BPart12Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact structural traversal and local numerical premises of the same full scalar reduction.",
        H("Exact P1 forest N25BPart12"),
        Blocks(
            Describe.Lean(DescribeId.Create("traversal-869"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart12.traversal_869"),
                H("Exact forest premise traversal_869"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact rational or structural premise is used in the complete forest check, which supplies the continuous real scalar inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("traversal-870"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart12.traversal_870"),
                H("Exact forest premise traversal_870"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact rational or structural premise is used in the complete forest check, which supplies the continuous real scalar inequality."))),
                DescribeRole.Theorem))));
}
