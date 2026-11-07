using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0770Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0770.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0770",
        H("Original frontier context coverage 0770"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36962", "selected_cut_36962", "Selected cut at depth 12, code 299060, node 986705",
                "At remaining fuel 9 and original index 986705, selection on the full partial prefix of depth 12 and code 299060 returns the complete row with depth 12, base-four code 299060, original node 986705, kind 2, reserved field 0, 2769 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37010", "selected_cut_37010", "Selected cut at depth 12, code 299126, node 987980",
                "At remaining fuel 9 and original index 987980, selection on the full partial prefix of depth 12 and code 299126 returns the complete row with depth 12, base-four code 299126, original node 987980, kind 2, reserved field 0, 1437 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-74765-986830", "unmarked_context_11_74765_986830", "Unmarked parent at depth 11, code 74765",
                "The frontier Boolean is false at remaining fuel 10, original node 986830, the whole prefixCache at depth 11 and code 74765, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-74780-987908", "unmarked_context_11_74780_987908", "Unmarked parent at depth 11, code 74780",
                "The frontier Boolean is false at remaining fuel 10, original node 987908, the whole prefixCache at depth 11 and code 74780, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-74765-986830", "node_context_11_74765_986830", "Original split at fuel 10 and node 986830",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 986705, 986747, 986785, 986829. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-74780-987908", "node_context_11_74780_987908", "Original split at fuel 10 and node 987908",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 987868, 987882, 987907. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-299060-986705", "context_12_299060_986705", "Context at depth 12, code 299060, node 986705",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299060 and original node 986705, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-299126-987980", "context_12_299126_987980", "Context at depth 12, code 299126, node 987980",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299126 and original node 987980, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
