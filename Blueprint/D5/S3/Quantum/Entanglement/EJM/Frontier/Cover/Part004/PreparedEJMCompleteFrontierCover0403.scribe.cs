using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0403Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0403.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0403",
        H("Original frontier context coverage 0403"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19347", "selected_cut_19347", "Selected cut at depth 12, code 72132, node 494061",
                "At remaining fuel 9 and original index 494061, selection on the full partial prefix of depth 12 and code 72132 returns the complete row with depth 12, base-four code 72132, original node 494061, kind 2, reserved field 0, 1085 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19394", "selected_cut_19394", "Selected cut at depth 13, code 288812, node 495408",
                "At remaining fuel 8 and original index 495408, selection on the full partial prefix of depth 13 and code 288812 returns the complete row with depth 13, base-four code 288812, original node 495408, kind 2, reserved field 0, 3965 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18032-494054", "unmarked_context_11_18032_494054", "Unmarked parent at depth 11, code 18032",
                "The frontier Boolean is false at remaining fuel 10, original node 494054, the whole prefixCache at depth 11 and code 18032, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72201-495320", "unmarked_context_12_72201_495320", "Unmarked parent at depth 12, code 72201",
                "The frontier Boolean is false at remaining fuel 9, original node 495320, the whole prefixCache at depth 12 and code 72201, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18032-494054", "node_context_11_18032_494054", "Original split at fuel 10 and node 494054",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 494013, 494028, 494046, 494053. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72201-495320", "node_context_12_72201_495320", "Original split at fuel 9 and node 495320",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 495228, 495268, 495287, 495319. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-18032-494054", "context_11_18032_494054", "Context at depth 11, code 18032, node 494054",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18032 and original node 494054, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_72128_494013, context_12_72129_494028, context_12_72130_494046, context_12_72131_494053.", DescribeRole.Theorem),
            Node("context-13-288812-495408", "context_13_288812_495408", "Context at depth 13, code 288812, node 495408",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288812 and original node 495408, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
