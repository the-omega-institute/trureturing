using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1062Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1062.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1062",
        H("Original frontier context coverage 1062"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50980", "selected_cut_50980", "Selected cut at depth 12, code 456733, node 1462968",
                "At remaining fuel 9 and original index 1462968, selection on the full partial prefix of depth 12 and code 456733 returns the complete row with depth 12, base-four code 456733, original node 1462968, kind 2, reserved field 0, 2089 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51027", "selected_cut_51027", "Selected cut at depth 11, code 114264, node 1465493",
                "At remaining fuel 10 and original index 1465493, selection on the full partial prefix of depth 11 and code 114264 returns the complete row with depth 11, base-four code 114264, original node 1465493, kind 2, reserved field 0, 1753 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-114183-1463038", "unmarked_context_11_114183_1463038", "Unmarked parent at depth 11, code 114183",
                "The frontier Boolean is false at remaining fuel 10, original node 1463038, the whole prefixCache at depth 11 and code 114183, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-7140-1465433", "unmarked_context_9_7140_1465433", "Unmarked parent at depth 9, code 7140",
                "The frontier Boolean is false at remaining fuel 12, original node 1465433, the whole prefixCache at depth 9 and code 7140, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-114183-1463038", "node_context_11_114183_1463038", "Original split at fuel 10 and node 1463038",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1461226, 1462968, 1463037, 296530. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-7140-1465433", "node_context_9_7140_1465433", "Original split at fuel 12 and node 1465433",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1464436, 1464804, 1465152, 1465432. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-456733-1462968", "context_12_456733_1462968", "Context at depth 12, code 456733, node 1462968",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 456733 and original node 1462968, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-114264-1465493", "context_11_114264_1465493", "Context at depth 11, code 114264, node 1465493",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 114264 and original node 1465493, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
