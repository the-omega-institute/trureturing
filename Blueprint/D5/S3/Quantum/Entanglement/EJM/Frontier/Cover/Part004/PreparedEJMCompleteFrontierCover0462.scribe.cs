using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0462Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0462.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0462",
        H("Original frontier context coverage 0462"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22179", "selected_cut_22179", "Selected cut at depth 13, code 302181, node 565438",
                "At remaining fuel 8 and original index 565438, selection on the full partial prefix of depth 13 and code 302181 returns the complete row with depth 13, base-four code 302181, original node 565438, kind 2, reserved field 0, 2129 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22226", "selected_cut_22226", "Selected cut at depth 13, code 302231, node 566444",
                "At remaining fuel 8 and original index 566444, selection on the full partial prefix of depth 13 and code 302231 returns the complete row with depth 13, base-four code 302231, original node 566444, kind 2, reserved field 0, 649 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75545-565469", "unmarked_context_12_75545_565469", "Unmarked parent at depth 12, code 75545",
                "The frontier Boolean is false at remaining fuel 9, original node 565469, the whole prefixCache at depth 12 and code 75545, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75557-566445", "unmarked_context_12_75557_566445", "Unmarked parent at depth 12, code 75557",
                "The frontier Boolean is false at remaining fuel 9, original node 566445, the whole prefixCache at depth 12 and code 75557, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75545-565469", "node_context_12_75545_565469", "Original split at fuel 9 and node 565469",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 565405, 565438, 565460, 565468. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75557-566445", "node_context_12_75557_566445", "Original split at fuel 9 and node 566445",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 566398, 566418, 566440, 566444. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-302181-565438", "context_13_302181_565438", "Context at depth 13, code 302181, node 565438",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302181 and original node 565438, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-75557-566445", "context_12_75557_566445", "Context at depth 12, code 75557, node 566445",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75557 and original node 566445, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_302228_566398, context_13_302229_566418, context_13_302230_566440, context_13_302231_566444.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
