using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0528Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0528.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0528",
        H("Original frontier context coverage 0528"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25347", "selected_cut_25347", "Selected cut at depth 12, code 87063, node 893",
                "At remaining fuel 9 and original index 893, selection on the full partial prefix of depth 12 and code 87063 returns the complete row with depth 12, base-four code 87063, original node 893, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25393", "selected_cut_25393", "Selected cut at depth 11, code 21781, node 451541",
                "At remaining fuel 10 and original index 451541, selection on the full partial prefix of depth 11 and code 21781 returns the complete row with depth 11, base-four code 21781, original node 451541, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-87062-641009", "unmarked_context_12_87062_641009", "Unmarked parent at depth 12, code 87062",
                "The frontier Boolean is false at remaining fuel 9, original node 641009, the whole prefixCache at depth 12 and code 87062, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1360-642293", "unmarked_context_9_1360_642293", "Unmarked parent at depth 9, code 1360",
                "The frontier Boolean is false at remaining fuel 12, original node 642293, the whole prefixCache at depth 9 and code 1360, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-87062-641009", "node_context_12_87062_641009", "Original split at fuel 9 and node 641009",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 640899, 640974, 640996, 641008. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1360-642293", "node_context_9_1360_642293", "Original split at fuel 12 and node 642293",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 640546, 641336, 642292, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-87062-641009", "context_12_87062_641009", "Context at depth 12, code 87062, node 641009",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 87062 and original node 641009, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_348248_640899, context_13_348249_640974, context_13_348250_640996, context_13_348251_641008.", DescribeRole.Theorem),
            Node("context-11-21781-451541", "context_11_21781_451541", "Context at depth 11, code 21781, node 451541",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 21781 and original node 451541, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
