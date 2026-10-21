using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class PreparedEJMCompleteFrontierDataTypesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierDataTypes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure original cut records and coordinate lookup",
        H("Pure original cut records and coordinate lookup"),
        Blocks(
            Paragraph(Text("These storage and lookup declarations are extracted from the existing complete-frontier types without changing their names or definitions. They use only Init. The mathematical frontier facade supplies metadata checks, canonical responses and response proofs separately.")),
            Node("cut-row", "CutRow", "Seven natural-number fields of an original cut row",
                "A row stores depth, kind, reserved, index, code, subtreeContexts and domain as natural numbers, with decidable equality. The fields themselves impose no metadata validity or acceptance condition."),
            Node("cut-table", "CutTable", "Empty, leaf and branching cut tables",
                "A table is empty, a leaf containing a row, or a branch carrying natural-number depth and code pivots and two child tables. The inductive type does not certify ordering, balancing or the stored rows."),
            Node("cut-table-lookup", "lookup", "Lookup by exact prefix depth and code",
                "An empty table returns none. A leaf returns its row exactly when both depth and code match. At a branch, lookup selects the left child when the requested depth is smaller than the pivot depth, or when depths agree and the requested code is smaller than the pivot code; otherwise it selects the right child. Lookup alone proves no response or original-DAG acceptance."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
