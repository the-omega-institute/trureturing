using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088;

internal sealed class PreparedEJMCompleteMiniCut01088Group14Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Group14.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cut 01088 normalized factor group 14",
        H("Cut 01088 normalized factor group 14"),
        Blocks(
            Paragraph(Text("This group joins original factor contributions 26 for events compatible with prefixPartial 13 17540. The normalized table is evaluated on the same event coordinates 14, 17, 19; normalization is an exact integer identity.")),
            Paragraph(Text("The scaled group table is defined by (6987435 : ℤ) * (435715267 + PreparedEJMCompleteMiniCut01088Tables.normal1878 x14 x17 x19). The proof of bound adds the actual factor inequalities and rewrites by the finite normalization receipt.")),
            Node("normalized-at", "normalizedAt", "Normalized contribution on an event",
                "The definition is PreparedEJMCompleteMiniCut01088Tables.normal1878 (e 14) (e 17) (e 19), with all arguments from the same original event.", DescribeRole.Definition),
            Node("table", "table", "Restore the integer scale and offset",
                "The table definition is (6987435 : ℤ) * (435715267 + PreparedEJMCompleteMiniCut01088Tables.normal1878 x14 x17 x19). Its argument order matches the corresponding factor tables.", DescribeRole.Definition),
            Node("normalization", "normalization", "Exact equality to the constituent factor tables",
                "For every tuple of the group's four-valued arguments, table equals the sum of the tables for factors 26. The proof reduces that full finite identity.", DescribeRole.Theorem),
            Node("lower-at", "lowerAt", "The scaled group lower value",
                "The definition evaluates table at global event coordinates 14, 17, 19 in that order.", DescribeRole.Definition),
            Node("score", "score", "Sum the matching original local scores",
                "The score is the sum of the actual local score contributions of factors 26 for the same event.", DescribeRole.Definition),
            Node("bound", "bound", "Group lower bound at the actual prefix",
                "For every event compatible with prefixPartial 13 17540, lowerAt is at most the group score. The proof combines the named constituent factor bounds and their exact normalization equation.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
