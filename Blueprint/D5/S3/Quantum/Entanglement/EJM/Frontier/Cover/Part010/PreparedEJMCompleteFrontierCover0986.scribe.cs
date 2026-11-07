using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0986Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0986.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0986",
        H("Original frontier context coverage 0986"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47331", "selected_cut_47331", "Selected cut at depth 12, code 373026, node 1324328",
                "At remaining fuel 9 and original index 1324328, selection on the full partial prefix of depth 12 and code 373026 returns the complete row with depth 12, base-four code 373026, original node 1324328, kind 2, reserved field 0, 1941 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47378", "selected_cut_47378", "Selected cut at depth 11, code 93281, node 1325664",
                "At remaining fuel 10 and original index 1325664, selection on the full partial prefix of depth 11 and code 93281 returns the complete row with depth 11, base-four code 93281, original node 1325664, kind 2, reserved field 0, 2077 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93256-1324359", "unmarked_context_11_93256_1324359", "Unmarked parent at depth 11, code 93256",
                "The frontier Boolean is false at remaining fuel 10, original node 1324359, the whole prefixCache at depth 11 and code 93256, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5829-1325631", "unmarked_context_9_5829_1325631", "Unmarked parent at depth 9, code 5829",
                "The frontier Boolean is false at remaining fuel 12, original node 1325631, the whole prefixCache at depth 9 and code 5829, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93256-1324359", "node_context_11_93256_1324359", "Original split at fuel 10 and node 1324359",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1324304, 1324328, 1324358. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5829-1325631", "node_context_9_5829_1325631", "Original split at fuel 12 and node 1325631",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1325246, 893098, 1325431, 1325630. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-373026-1324328", "context_12_373026_1324328", "Context at depth 12, code 373026, node 1324328",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 373026 and original node 1324328, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-93281-1325664", "context_11_93281_1325664", "Context at depth 11, code 93281, node 1325664",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93281 and original node 1325664, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
