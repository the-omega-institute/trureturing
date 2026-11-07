using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0351Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0351.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0351",
        H("Original frontier context coverage 0351"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16852", "selected_cut_16852", "Selected cut at depth 13, code 113890, node 428732",
                "At remaining fuel 8 and original index 428732, selection on the full partial prefix of depth 13 and code 113890 returns the complete row with depth 13, base-four code 113890, original node 428732, kind 2, reserved field 0, 1737 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16898", "selected_cut_16898", "Selected cut at depth 13, code 113936, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 113936 returns the complete row with depth 13, base-four code 113936, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28472-428740", "unmarked_context_12_28472_428740", "Unmarked parent at depth 12, code 28472",
                "The frontier Boolean is false at remaining fuel 9, original node 428740, the whole prefixCache at depth 12 and code 28472, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-7120-429716", "unmarked_context_11_7120_429716", "Unmarked parent at depth 11, code 7120",
                "The frontier Boolean is false at remaining fuel 10, original node 429716, the whole prefixCache at depth 11 and code 7120, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28472-428740", "node_context_12_28472_428740", "Original split at fuel 9 and node 428740",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 428660, 428705, 428732, 428739. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-7120-429716", "node_context_11_7120_429716", "Original split at fuel 10 and node 429716",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 429374, 429547, 429625, 429715. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-113890-428732", "context_13_113890_428732", "Context at depth 13, code 113890, node 428732",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113890 and original node 428732, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-113936-3444", "context_13_113936_3444", "Context at depth 13, code 113936, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113936 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
