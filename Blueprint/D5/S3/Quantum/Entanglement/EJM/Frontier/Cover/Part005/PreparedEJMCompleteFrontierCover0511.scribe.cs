using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0511Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0511.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0511",
        H("Original frontier context coverage 0511"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24531", "selected_cut_24531", "Selected cut at depth 12, code 77196, node 620173",
                "At remaining fuel 9 and original index 620173, selection on the full partial prefix of depth 12 and code 77196 returns the complete row with depth 12, base-four code 77196, original node 620173, kind 2, reserved field 0, 2185 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24579", "selected_cut_24579", "Selected cut at depth 11, code 19311, node 621306",
                "At remaining fuel 10 and original index 621306, selection on the full partial prefix of depth 11 and code 19311 returns the complete row with depth 11, base-four code 19311, original node 621306, kind 2, reserved field 0, 3717 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19299-620269", "unmarked_context_11_19299_620269", "Unmarked parent at depth 11, code 19299",
                "The frontier Boolean is false at remaining fuel 10, original node 620269, the whole prefixCache at depth 11 and code 19299, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19310-621252", "unmarked_context_11_19310_621252", "Unmarked parent at depth 11, code 19310",
                "The frontier Boolean is false at remaining fuel 10, original node 621252, the whole prefixCache at depth 11 and code 19310, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19299-620269", "node_context_11_19299_620269", "Original split at fuel 10 and node 620269",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 620173, 620200, 620237, 620268. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19310-621252", "node_context_11_19310_621252", "Original split at fuel 10 and node 621252",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 621200, 621217, 621232, 621251. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-77196-620173", "context_12_77196_620173", "Context at depth 12, code 77196, node 620173",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77196 and original node 620173, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-19311-621306", "context_11_19311_621306", "Context at depth 11, code 19311, node 621306",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19311 and original node 621306, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
