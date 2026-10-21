using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal;

internal sealed class N30APart08Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact structural traversal and local numerical premises of the same full scalar reduction.",
        H("Exact P1 forest N30APart08"),
        Blocks(
            Describe.Lean(DescribeId.Create("traversal-566"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart08.traversal_566"),
                H("Exact forest premise traversal_566"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact rational or structural premise is used in the complete forest check, which supplies the continuous real scalar inequality."))),
                DescribeRole.Theorem))));
}
