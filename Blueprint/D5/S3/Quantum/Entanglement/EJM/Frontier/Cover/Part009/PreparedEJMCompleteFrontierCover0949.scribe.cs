using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0949Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0949.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0949",
        H("Original frontier context coverage 0949"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45555", "selected_cut_45555", "Selected cut at depth 12, code 368193, node 1265093",
                "At remaining fuel 9 and original index 1265093, selection on the full partial prefix of depth 12 and code 368193 returns the complete row with depth 12, base-four code 368193, original node 1265093, kind 2, reserved field 0, 2153 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45603", "selected_cut_45603", "Selected cut at depth 11, code 92082, node 1266599",
                "At remaining fuel 10 and original index 1266599, selection on the full partial prefix of depth 11 and code 92082 returns the complete row with depth 11, base-four code 92082, original node 1266599, kind 2, reserved field 0, 709 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92048-1265182", "unmarked_context_11_92048_1265182", "Unmarked parent at depth 11, code 92048",
                "The frontier Boolean is false at remaining fuel 10, original node 1265182, the whole prefixCache at depth 11 and code 92048, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5754-1266525", "unmarked_context_9_5754_1266525", "Unmarked parent at depth 9, code 5754",
                "The frontier Boolean is false at remaining fuel 12, original node 1266525, the whole prefixCache at depth 9 and code 5754, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92048-1265182", "node_context_11_92048_1265182", "Original split at fuel 10 and node 1265182",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1173556, 1265093, 1265139, 1265181. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5754-1266525", "node_context_9_5754_1266525", "Original split at fuel 12 and node 1266525",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1266236, 1266396, 1266450, 1266524. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-368193-1265093", "context_12_368193_1265093", "Context at depth 12, code 368193, node 1265093",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 368193 and original node 1265093, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-92082-1266599", "context_11_92082_1266599", "Context at depth 11, code 92082, node 1266599",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92082 and original node 1266599, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
