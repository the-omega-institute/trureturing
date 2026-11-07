using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088;

internal sealed class PreparedEJMCompleteMiniCut01088Factor21Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Factor21.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cut 01088 local score factor 21",
        H("Cut 01088 local score factor 21"),
        Blocks(
            Paragraph(Text("Assignments have twenty coordinates with four values each. This factor is used only under compatibility with the actual depth-thirteen prefix of code 17540. Its local score is EJMInflationScore.singletonBlock F2 5 e. The table arguments read global coordinates 14, 16, 18 from the same event.")),
            Paragraph(Text("The singleton state is obtained by the original cache updates from its literal row and local symmetry. completedPartial fills just this factor's required coordinates from the event. The assignment_receipt equates the complete cached assignment with the transformed local projection; cache soundness then bounds the score.")),
            Node("table", "table", "The exact local lower table",
                "The table has 3 four-valued arguments corresponding to global coordinates 14, 16, 18. Its integer value is the original cached row lower bound after the stated local updates; the row index and local symmetry remain part of the state.", DescribeRole.Definition),
            Node("lower-at", "lowerAt", "Evaluate the lower table on the same event",
                "The event lower bound reads coordinates 14, 16, 18 and passes them in that order to table.", DescribeRole.Definition),
            Node("score", "score", "The original local score contribution",
                "The score definition is EJMInflationScore.singletonBlock F2 5 e. Group bounds combine this contribution with other original factor scores.", DescribeRole.Definition),
            Node("bound", "bound", "Bound the local score under the actual prefix",
                "For every event compatible with prefixPartial 13 17540, lowerAt is at most this factor score on that same event. The proof fills the necessary coordinates compatibly, obtains local validity from assignment_receipt, projects event compatibility, and applies the corresponding original valid-lower theorem.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
