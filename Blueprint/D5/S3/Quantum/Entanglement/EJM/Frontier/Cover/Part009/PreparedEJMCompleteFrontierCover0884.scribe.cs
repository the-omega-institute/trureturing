using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0884Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0884.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0884",
        H("Original frontier context coverage 0884"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42436", "selected_cut_42436", "Selected cut at depth 11, code 84496, node 1159893",
                "At remaining fuel 10 and original index 1159893, selection on the full partial prefix of depth 11 and code 84496 returns the complete row with depth 11, base-four code 84496, original node 1159893, kind 2, reserved field 0, 2957 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42482", "selected_cut_42482", "Selected cut at depth 12, code 338063, node 1160828",
                "At remaining fuel 9 and original index 1160828, selection on the full partial prefix of depth 12 and code 338063 returns the complete row with depth 12, base-four code 338063, original node 1160828, kind 2, reserved field 0, 1209 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84495-1159814", "unmarked_context_11_84495_1159814", "Unmarked parent at depth 11, code 84495",
                "The frontier Boolean is false at remaining fuel 10, original node 1159814, the whole prefixCache at depth 11 and code 84495, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84515-1160829", "unmarked_context_11_84515_1160829", "Unmarked parent at depth 11, code 84515",
                "The frontier Boolean is false at remaining fuel 10, original node 1160829, the whole prefixCache at depth 11 and code 84515, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84495-1159814", "node_context_11_84495_1159814", "Original split at fuel 10 and node 1159814",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1159781, 1159813, 1120582. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84515-1160829", "node_context_11_84515_1160829", "Original split at fuel 10 and node 1160829",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1160776, 1160794, 1160808, 1160828. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84495-1159814", "context_11_84495_1159814", "Context at depth 11, code 84495, node 1159814",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84495 and original node 1159814, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_337980_1108174, context_12_337981_1159781, context_12_337982_1159813, context_12_337983_1120582.", DescribeRole.Theorem),
            Node("context-11-84515-1160829", "context_11_84515_1160829", "Context at depth 11, code 84515, node 1160829",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84515 and original node 1160829, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_338060_1160776, context_12_338061_1160794, context_12_338062_1160808, context_12_338063_1160828.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
