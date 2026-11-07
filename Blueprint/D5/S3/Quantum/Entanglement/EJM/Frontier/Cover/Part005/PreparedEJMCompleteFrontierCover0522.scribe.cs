using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0522Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0522.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0522",
        H("Original frontier context coverage 0522"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25060", "selected_cut_25060", "Selected cut at depth 13, code 310444, node 633840",
                "At remaining fuel 8 and original index 633840, selection on the full partial prefix of depth 13 and code 310444 returns the complete row with depth 13, base-four code 310444, original node 633840, kind 2, reserved field 0, 701 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25108", "selected_cut_25108", "Selected cut at depth 13, code 310507, node 634676",
                "At remaining fuel 8 and original index 634676, selection on the full partial prefix of depth 13 and code 310507 returns the complete row with depth 13, base-four code 310507, original node 634676, kind 2, reserved field 0, 841 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77611-633903", "unmarked_context_12_77611_633903", "Unmarked parent at depth 12, code 77611",
                "The frontier Boolean is false at remaining fuel 9, original node 633903, the whole prefixCache at depth 12 and code 77611, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77625-634599", "unmarked_context_12_77625_634599", "Unmarked parent at depth 12, code 77625",
                "The frontier Boolean is false at remaining fuel 9, original node 634599, the whole prefixCache at depth 12 and code 77625, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77611-633903", "node_context_12_77611_633903", "Original split at fuel 9 and node 633903",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 633840, 633872, 633894, 633902. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77625-634599", "node_context_12_77625_634599", "Original split at fuel 9 and node 634599",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 634509, 634559, 634583, 634598. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-310444-633840", "context_13_310444_633840", "Context at depth 13, code 310444, node 633840",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 310444 and original node 633840, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-310507-634676", "context_13_310507_634676", "Context at depth 13, code 310507, node 634676",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 310507 and original node 634676, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
