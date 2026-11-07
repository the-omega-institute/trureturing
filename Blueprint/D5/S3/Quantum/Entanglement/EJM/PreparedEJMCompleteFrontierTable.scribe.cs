using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class PreparedEJMCompleteFrontierTableDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierTable.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original cut table",
        H("The complete original cut table"),
        Blocks(
            Paragraph(Text("The full binary tree joins all 207 chunks, from chunk 000 through chunk 206, preserving each depth/code pivot and the complete row at each leaf. The response assembly has exactly the corresponding conjunction structure.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("cut-table", "cutTable", "Join every original cut chunk",
                "The definition connects the 207 literal CutTable chunks through their lexicographic depth/code branch pivots; selection uses this exact cutTable.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
