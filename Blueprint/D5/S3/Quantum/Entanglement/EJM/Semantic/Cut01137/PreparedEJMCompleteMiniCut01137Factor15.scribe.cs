using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137;

internal sealed class PreparedEJMCompleteMiniCut01137Factor15Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Factor15.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cut 01137 local score factor 15",
        H("Cut 01137 local score factor 15"),
        Blocks(
            Paragraph(Text("Assignments have twenty coordinates with four values each. This factor is used only under compatibility with the actual depth-thirteen prefix of code 17589. Its local score is EJMInflationScore.triangleBlock F1 15 e. The table arguments read global coordinates 13, 18, 19 from the same event.")),
            Paragraph(Text("The triangle state is obtained by the original cache updates from its literal row and local symmetry. completedPartial fills just this factor's required coordinates from the event. The assignment_receipt equates the complete cached assignment with the transformed local projection; cache soundness then bounds the score.")),
            Node("table", "table", "The exact local lower table",
                "The table has 3 four-valued arguments corresponding to global coordinates 13, 18, 19. Its integer value is the original cached row lower bound after the stated local updates; the row index and local symmetry remain part of the state.", DescribeRole.Definition),
            Node("lower-at", "lowerAt", "Evaluate the lower table on the same event",
                "The event lower bound reads coordinates 13, 18, 19 and passes them in that order to table.", DescribeRole.Definition),
            Node("score", "score", "The original local score contribution",
                "The score definition is EJMInflationScore.triangleBlock F1 15 e. Group bounds combine this contribution with other original factor scores.", DescribeRole.Definition),
            Node("bound", "bound", "Bound the local score under the actual prefix",
                "For every event compatible with prefixPartial 13 17589, lowerAt is at most this factor score on that same event. The proof fills the necessary coordinates compatibly, obtains local validity from assignment_receipt, projects event compatibility, and applies the corresponding original valid-lower theorem.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
