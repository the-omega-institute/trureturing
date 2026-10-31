using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Encoding;

internal sealed class EJMOriginalDAGBlock07Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Encoding/EJMOriginalDAGBlock07.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal original EJM DAG records 07",
        H("Literal original EJM DAG records 07"),
        Blocks(
            Paragraph(Text("This block proposes the original chunk words without a correctness or acceptance assertion. Native record IDs, exact action pivots, split coordinates and all four children remain literal inputs to the full original replay.")),
            Node("chunks", "chunks", "Original literal chunk storage",
                "The balanced tree retains every proposed chunk index and its original packed 103-bit records. Each reached record is still interpreted and checked in its own actual replay context.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
