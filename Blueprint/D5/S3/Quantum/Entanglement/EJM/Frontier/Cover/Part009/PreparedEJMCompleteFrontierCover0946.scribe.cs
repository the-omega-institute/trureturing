using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0946Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0946.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0946",
        H("Original frontier context coverage 0946"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45412", "selected_cut_45412", "Selected cut at depth 12, code 367408, node 766630",
                "At remaining fuel 9 and original index 766630, selection on the full partial prefix of depth 12 and code 367408 returns the complete row with depth 12, base-four code 367408, original node 766630, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45459", "selected_cut_45459", "Selected cut at depth 12, code 367647, node 1261198",
                "At remaining fuel 9 and original index 1261198, selection on the full partial prefix of depth 12 and code 367647 returns the complete row with depth 12, base-four code 367647, original node 1261198, kind 2, reserved field 0, 2245 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22962-1259000", "unmarked_context_10_22962_1259000", "Unmarked parent at depth 10, code 22962",
                "The frontier Boolean is false at remaining fuel 11, original node 1259000, the whole prefixCache at depth 10 and code 22962, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-91910-1260962", "unmarked_context_11_91910_1260962", "Unmarked parent at depth 11, code 91910",
                "The frontier Boolean is false at remaining fuel 10, original node 1260962, the whole prefixCache at depth 11 and code 91910, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22962-1259000", "node_context_10_22962_1259000", "Original split at fuel 11 and node 1259000",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1258653, 1258880, 900587, 1258999. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-91910-1260962", "node_context_11_91910_1260962", "Original split at fuel 10 and node 1260962",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994572, 1260887, 806997, 1260961. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-22962-1259000", "context_10_22962_1259000", "Context at depth 10, code 22962, node 1259000",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22962 and original node 1259000, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_91848_1258653, context_11_91849_1258880, context_11_91850_900587, context_11_91851_1258999.", DescribeRole.Theorem),
            Node("context-12-367647-1261198", "context_12_367647_1261198", "Context at depth 12, code 367647, node 1261198",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 367647 and original node 1261198, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
