using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0962Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0962.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0962",
        H("Original frontier context coverage 0962"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46179", "selected_cut_46179", "Selected cut at depth 11, code 92496, node 1283168",
                "At remaining fuel 10 and original index 1283168, selection on the full partial prefix of depth 11 and code 92496 returns the complete row with depth 11, base-four code 92496, original node 1283168, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46226", "selected_cut_46226", "Selected cut at depth 12, code 370187, node 1287742",
                "At remaining fuel 9 and original index 1287742, selection on the full partial prefix of depth 12 and code 370187 returns the complete row with depth 12, base-four code 370187, original node 1287742, kind 2, reserved field 0, 3545 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-5780-1286474", "unmarked_context_9_5780_1286474", "Unmarked parent at depth 9, code 5780",
                "The frontier Boolean is false at remaining fuel 12, original node 1286474, the whole prefixCache at depth 9 and code 5780, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92546-1287743", "unmarked_context_11_92546_1287743", "Unmarked parent at depth 11, code 92546",
                "The frontier Boolean is false at remaining fuel 10, original node 1287743, the whole prefixCache at depth 11 and code 92546, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-5780-1286474", "node_context_9_5780_1286474", "Original split at fuel 12 and node 1286474",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1285054, 1285490, 1286030, 1286473. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92546-1287743", "node_context_11_92546_1287743", "Original split at fuel 10 and node 1287743",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1287657, 893903, 1287742. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-5780-1286474", "context_9_5780_1286474", "Context at depth 9, code 5780, node 1286474",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 5780 and original node 1286474, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_23120_1285054, context_10_23121_1285490, context_10_23122_1286030, context_10_23123_1286473.", DescribeRole.Theorem),
            Node("context-11-92546-1287743", "context_11_92546_1287743", "Context at depth 11, code 92546, node 1287743",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92546 and original node 1287743, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_370184_448748, context_12_370185_1287657, context_12_370186_893903, context_12_370187_1287742.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
