using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0012Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0012.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0012",
        H("Original frontier context coverage 0012"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00578", "selected_cut_00578", "Selected cut at depth 14, code 24773, node 25965",
                "At remaining fuel 7 and original index 25965, selection on the full partial prefix of depth 14 and code 24773 returns the complete row with depth 14, base-four code 24773, original node 25965, kind 2, reserved field 0, 1453 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00626", "selected_cut_00626", "Selected cut at depth 13, code 6239, node 27561",
                "At remaining fuel 8 and original index 27561, selection on the full partial prefix of depth 13 and code 6239 returns the complete row with depth 13, base-four code 6239, original node 27561, kind 2, reserved field 0, 1449 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-6193-26056", "unmarked_context_13_6193_26056", "Unmarked parent at depth 13, code 6193",
                "The frontier Boolean is false at remaining fuel 8, original node 26056, the whole prefixCache at depth 13 and code 6193, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-6237-27478", "unmarked_context_13_6237_27478", "Unmarked parent at depth 13, code 6237",
                "The frontier Boolean is false at remaining fuel 8, original node 27478, the whole prefixCache at depth 13 and code 6237, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-6193-26056", "node_context_13_6193_26056", "Original split at fuel 8 and node 26056",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 25924, 25965, 26008, 26055. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-6237-27478", "node_context_13_6237_27478", "Original split at fuel 8 and node 27478",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 27436, 27451, 27465, 27477. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-24773-25965", "context_14_24773_25965", "Context at depth 14, code 24773, node 25965",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 24773 and original node 25965, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-6239-27561", "context_13_6239_27561", "Context at depth 13, code 6239, node 27561",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 6239 and original node 27561, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
