using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0627Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0627.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0627",
        H("Original frontier context coverage 0627"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30100", "selected_cut_30100", "Selected cut at depth 13, code 376033, node 759575",
                "At remaining fuel 8 and original index 759575, selection on the full partial prefix of depth 13 and code 376033 returns the complete row with depth 13, base-four code 376033, original node 759575, kind 2, reserved field 0, 2349 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30147", "selected_cut_30147", "Selected cut at depth 12, code 94041, node 642341",
                "At remaining fuel 9 and original index 642341, selection on the full partial prefix of depth 12 and code 94041 returns the complete row with depth 12, base-four code 94041, original node 642341, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-94008-759605", "unmarked_context_12_94008_759605", "Unmarked parent at depth 12, code 94008",
                "The frontier Boolean is false at remaining fuel 9, original node 759605, the whole prefixCache at depth 12 and code 94008, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23509-760805", "unmarked_context_11_23509_760805", "Unmarked parent at depth 11, code 23509",
                "The frontier Boolean is false at remaining fuel 10, original node 760805, the whole prefixCache at depth 11 and code 23509, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-94008-759605", "node_context_12_94008_759605", "Original split at fuel 9 and node 759605",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 759527, 759575, 759595, 759604. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23509-760805", "node_context_11_23509_760805", "Original split at fuel 10 and node 760805",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 760720, 642341, 760765, 760804. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-376033-759575", "context_13_376033_759575", "Context at depth 13, code 376033, node 759575",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 376033 and original node 759575, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-94041-642341", "context_12_94041_642341", "Context at depth 12, code 94041, node 642341",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 94041 and original node 642341, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
