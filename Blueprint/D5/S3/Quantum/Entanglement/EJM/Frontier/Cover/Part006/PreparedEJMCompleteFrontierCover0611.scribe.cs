using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0611Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0611.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0611",
        H("Original frontier context coverage 0611"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29331", "selected_cut_29331", "Selected cut at depth 12, code 93477, node 719134",
                "At remaining fuel 9 and original index 719134, selection on the full partial prefix of depth 12 and code 93477 returns the complete row with depth 12, base-four code 93477, original node 719134, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29379", "selected_cut_29379", "Selected cut at depth 13, code 373959, node 741744",
                "At remaining fuel 8 and original index 741744, selection on the full partial prefix of depth 13 and code 373959 returns the complete row with depth 13, base-four code 373959, original node 741744, kind 2, reserved field 0, 837 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93478-740986", "unmarked_context_12_93478_740986", "Unmarked parent at depth 12, code 93478",
                "The frontier Boolean is false at remaining fuel 9, original node 740986, the whole prefixCache at depth 12 and code 93478, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93488-741685", "unmarked_context_12_93488_741685", "Unmarked parent at depth 12, code 93488",
                "The frontier Boolean is false at remaining fuel 9, original node 741685, the whole prefixCache at depth 12 and code 93488, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93478-740986", "node_context_12_93478_740986", "Original split at fuel 9 and node 740986",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 740929, 740956, 740976, 740985. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93488-741685", "node_context_12_93488_741685", "Original split at fuel 9 and node 741685",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 741631, 741656, 741676, 741684. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93477-719134", "context_12_93477_719134", "Context at depth 12, code 93477, node 719134",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93477 and original node 719134, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-373959-741744", "context_13_373959_741744", "Context at depth 13, code 373959, node 741744",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 373959 and original node 741744, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
