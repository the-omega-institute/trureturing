using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088;

internal sealed class PreparedEJMCompleteMiniCut01088Factor28Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Factor28.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cut 01088 local score factor 28",
        H("Cut 01088 local score factor 28"),
        Blocks(
            Paragraph(Text("Assignments have twenty coordinates with four values each. This factor is used only under compatibility with the actual depth-thirteen prefix of code 17540. Its local score is singletonBlock F2 12 e. The table arguments read global coordinates 13, 15, 16 from the same event.")),
            Paragraph(Text("This factor transfers singleton block twelve from prefix code 17589 to code 17540. The canonical event fills the source prefix and uses the original event elsewhere. The two prefixes agree on the entire lhsSingleton twelve projection; the proof preserves that local score and future coordinates thirteen, fifteen and sixteen before applying the source factor bound. Equality of the two full prefixes is not assumed.")),
            Node("table", "table", "The exact local lower table",
                "The table has 3 four-valued arguments corresponding to global coordinates 13, 15, 16. It directly uses the source singleton factor table under the projection-preserving transfer described above.", DescribeRole.Definition),
            Node("lower-at", "lowerAt", "Evaluate the lower table on the same event",
                "The event lower bound reads coordinates 13, 15, 16 and passes them in that order to table.", DescribeRole.Definition),
            Node("score", "score", "The original local score contribution",
                "The score definition is singletonBlock F2 12 e. Group bounds combine this contribution with other original factor scores.", DescribeRole.Definition),
            Node("bound", "bound", "Bound the local score under the actual prefix",
                "For every event compatible with prefixPartial 13 17540, lowerAt is at most this factor score on that same event. The proof transfers the source bound through the canonical event and proven projection and score equalities.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
