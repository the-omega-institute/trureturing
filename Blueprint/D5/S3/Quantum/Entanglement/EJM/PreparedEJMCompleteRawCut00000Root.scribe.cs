using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class PreparedEJMCompleteRawCut00000RootDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteRawCut00000Root.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original suffix assembly at depth 12, code 0, node 415",
        H("Original suffix assembly at depth 12, code 0, node 415"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The root exposes the matching replay-parts conclusion for use by the corresponding raw_cut response. It keeps the original Accepted proposition in full.")),
            Node("accepted-actual-context", "accepted_actual_context", "The assembled original context",
                "The statement is Accepted at depth 12, code 0, original index 415 and remaining fuel 9, with its whole canonical prefix cache and partial assignment. The proof directly uses accepted_12_0_415 from the imported replay parts.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
