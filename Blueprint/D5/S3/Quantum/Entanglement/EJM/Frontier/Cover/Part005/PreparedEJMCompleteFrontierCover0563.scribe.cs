using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0563Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0563.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0563",
        H("Original frontier context coverage 0563"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27027", "selected_cut_27027", "Selected cut at depth 12, code 91242, node 683684",
                "At remaining fuel 9 and original index 683684, selection on the full partial prefix of depth 12 and code 91242 returns the complete row with depth 12, base-four code 91242, original node 683684, kind 2, reserved field 0, 2993 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27074", "selected_cut_27074", "Selected cut at depth 12, code 91283, node 685154",
                "At remaining fuel 9 and original index 685154, selection on the full partial prefix of depth 12 and code 91283 returns the complete row with depth 12, base-four code 91283, original node 685154, kind 2, reserved field 0, 2077 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-22810-683730", "unmarked_context_11_22810_683730", "Unmarked parent at depth 11, code 22810",
                "The frontier Boolean is false at remaining fuel 10, original node 683730, the whole prefixCache at depth 11 and code 22810, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-5704-685041", "unmarked_context_10_5704_685041", "Unmarked parent at depth 10, code 5704",
                "The frontier Boolean is false at remaining fuel 11, original node 685041, the whole prefixCache at depth 10 and code 5704, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-22810-683730", "node_context_11_22810_683730", "Original split at fuel 10 and node 683730",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 683552, 683644, 683684, 683729. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-5704-685041", "node_context_10_5704_685041", "Original split at fuel 11 and node 685041",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 684703, 684799, 684935, 685040. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-91242-683684", "context_12_91242_683684", "Context at depth 12, code 91242, node 683684",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91242 and original node 683684, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-91283-685154", "context_12_91283_685154", "Context at depth 12, code 91283, node 685154",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91283 and original node 685154, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
