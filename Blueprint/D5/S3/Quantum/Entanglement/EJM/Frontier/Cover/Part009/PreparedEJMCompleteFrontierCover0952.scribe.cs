using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0952Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0952.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0952",
        H("Original frontier context coverage 0952"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45699", "selected_cut_45699", "Selected cut at depth 11, code 92196, node 1269656",
                "At remaining fuel 10 and original index 1269656, selection on the full partial prefix of depth 11 and code 92196 returns the complete row with depth 11, base-four code 92196, original node 1269656, kind 2, reserved field 0, 1833 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45746", "selected_cut_45746", "Selected cut at depth 12, code 368936, node 435790",
                "At remaining fuel 9 and original index 435790, selection on the full partial prefix of depth 12 and code 368936 returns the complete row with depth 12, base-four code 368936, original node 435790, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23048-1269621", "unmarked_context_10_23048_1269621", "Unmarked parent at depth 10, code 23048",
                "The frontier Boolean is false at remaining fuel 11, original node 1269621, the whole prefixCache at depth 10 and code 23048, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92233-1271416", "unmarked_context_11_92233_1271416", "Unmarked parent at depth 11, code 92233",
                "The frontier Boolean is false at remaining fuel 10, original node 1271416, the whole prefixCache at depth 11 and code 92233, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23048-1269621", "node_context_10_23048_1269621", "Original split at fuel 11 and node 1269621",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 1269530, 1269585, 1269620. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92233-1271416", "node_context_11_92233_1271416", "Original split at fuel 10 and node 1271416",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1271301, 891951, 1271349, 1271415. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23048-1269621", "context_10_23048_1269621", "Context at depth 10, code 23048, node 1269621",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23048 and original node 1269621, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_92192_907917, context_11_92193_1269530, context_11_92194_1269585, context_11_92195_1269620.", DescribeRole.Theorem),
            Node("context-12-368936-435790", "context_12_368936_435790", "Context at depth 12, code 368936, node 435790",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 368936 and original node 435790, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
