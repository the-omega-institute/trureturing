using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0158Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0158.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0158",
        H("Original frontier context coverage 0158"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07587", "selected_cut_07587", "Selected cut at depth 13, code 90354, node 219154",
                "At remaining fuel 8 and original index 219154, selection on the full partial prefix of depth 13 and code 90354 returns the complete row with depth 13, base-four code 90354, original node 219154, kind 2, reserved field 0, 1341 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07633", "selected_cut_07633", "Selected cut at depth 13, code 90400, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 90400 returns the complete row with depth 13, base-four code 90400, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22588-219163", "unmarked_context_12_22588_219163", "Unmarked parent at depth 12, code 22588",
                "The frontier Boolean is false at remaining fuel 9, original node 219163, the whole prefixCache at depth 12 and code 22588, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5649-219946", "unmarked_context_11_5649_219946", "Unmarked parent at depth 11, code 5649",
                "The frontier Boolean is false at remaining fuel 10, original node 219946, the whole prefixCache at depth 11 and code 5649, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22588-219163", "node_context_12_22588_219163", "Original split at fuel 9 and node 219163",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 219099, 219136, 219154, 219162. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5649-219946", "node_context_11_5649_219946", "Original split at fuel 10 and node 219946",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 219807, 219808, 219872, 219945. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-90354-219154", "context_13_90354_219154", "Context at depth 13, code 90354, node 219154",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90354 and original node 219154, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-90400-3444", "context_13_90400_3444", "Context at depth 13, code 90400, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90400 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
