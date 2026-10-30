using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0364Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0364.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0364",
        H("Original frontier context coverage 0364"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17474", "selected_cut_17474", "Selected cut at depth 12, code 70178, node 444699",
                "At remaining fuel 9 and original index 444699, selection on the full partial prefix of depth 12 and code 70178 returns the complete row with depth 12, base-four code 70178, original node 444699, kind 2, reserved field 0, 3569 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17521", "selected_cut_17521", "Selected cut at depth 12, code 70195, node 445792",
                "At remaining fuel 9 and original index 445792, selection on the full partial prefix of depth 12 and code 70195 returns the complete row with depth 12, base-four code 70195, original node 445792, kind 2, reserved field 0, 3585 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-70179-444767", "unmarked_context_12_70179_444767", "Unmarked parent at depth 12, code 70179",
                "The frontier Boolean is false at remaining fuel 9, original node 444767, the whole prefixCache at depth 12 and code 70179, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-17548-445793", "unmarked_context_11_17548_445793", "Unmarked parent at depth 11, code 17548",
                "The frontier Boolean is false at remaining fuel 10, original node 445793, the whole prefixCache at depth 11 and code 17548, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-70179-444767", "node_context_12_70179_444767", "Original split at fuel 9 and node 444767",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 444720, 444737, 444757, 444766. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-17548-445793", "node_context_11_17548_445793", "Original split at fuel 10 and node 445793",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 445562, 445640, 445715, 445792. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-70178-444699", "context_12_70178_444699", "Context at depth 12, code 70178, node 444699",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 70178 and original node 444699, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-17548-445793", "context_11_17548_445793", "Context at depth 11, code 17548, node 445793",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 17548 and original node 445793, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_70192_445562, context_12_70193_445640, context_12_70194_445715, context_12_70195_445792.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
