using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMLocalCacheDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact actual local-row and action data",
        H("Compact actual local-row and action data"),
        Blocks(
            Paragraph(Text("The exact coefficient score and scale remain unchanged. A row mirror records a literal base-five hash, its already scaled integer lower, coordinate-slot proposals and 25-bit next-row/action proposals. None of these definitions proves the mirror or a transition is correct. The complete kernel receipts compare every original raw hash and scaled lower once, then a proved generic bridge recovers the whole assignment equality with the original 164-bit decoder. Every unknown-coordinate/value transition is still checked over its entire assignment. The literal incidence maps refer to the original sixteen triangle and sixteen singleton blocks.")),
            Node("mirror-row", "MirrorRow", "Small literal fields and per-row transitions",
                "The hash and integer lower are stored as direct literals. Each unknown coordinate has all four 25-bit transition words, so no actual branch is discarded.", DescribeRole.Definition),
            Node("mirror-tree-get", "get", "Total binary lookup of a proposed mirror",
                "Lookup follows literal indices and returns a zero row at an empty tree. Exact mirrors must therefore be earned by finite-domain receipts, including every actual row index.", DescribeRole.Definition),
            Node("check-raw-mirror", "checkRawMirror", "Check the original raw hash and scaled lower once",
                "The terminal or branch row must have the exact literal mirror hash and the same lower multiplied by the original scale. This checker supplies no external numerical premise.", DescribeRole.Definition),
            Node("checked-raw-mirror-eq", "checked_raw_mirror_eq", "Checked raw fields preserve the complete original assignment",
                "For arbitrary positive coordinate dimension and row count, acceptance entails equality of the whole original partial-event function and of the exact scaled lower. Both original row constructors are covered by the same symbolic proof.", DescribeRole.Theorem),
            Node("read-transition", "readTransition", "Decode one row/action proposal",
                "The four-bit coordinate slot chooses one of four consecutive 25-bit words. Sixteen bits hold the proposed next row and nine bits hold the action. Modular finite-index conversions supply totality and no semantic correctness premise.", DescribeRole.Definition),
            Node("triangle-compose", "triangleCompose", "Compose exact triangle actions in the required order",
                "Applying the new action t after the old action s uses coordinate map pi_s composed with pi_t and outcome map o_t composed with o_s. The multiplication and inverse tables receive separate actual function-law receipts.", DescribeRole.Definition),
            Node("singleton-compose", "singletonCompose", "Compose exact singleton actions",
                "The same action order uses the actual singleton coordinate table; agreement with the concrete partial action is proved by the companion cache laws.", DescribeRole.Definition),
            Node("triangle-incidence", "triangleIncidence", "Original triangle-block incidence",
                "For each global node and original block, the table proposes its unique local coordinate or none. The actual incidence laws check this against lhsTriangle and preserve the entire projection on unaffected blocks.", DescribeRole.Definition),
            Node("singleton-incidence", "singletonIncidence", "Original singleton-block incidence",
                "This is the analogous actual nine-coordinate block table, checked against lhsSingleton before any update uses it.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
