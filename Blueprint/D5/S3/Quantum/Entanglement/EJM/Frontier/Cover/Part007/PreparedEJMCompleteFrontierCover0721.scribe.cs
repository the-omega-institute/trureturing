using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0721Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0721.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0721",
        H("Original frontier context coverage 0721"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34611", "selected_cut_34611", "Selected cut at depth 11, code 70284, node 900903",
                "At remaining fuel 10 and original index 900903, selection on the full partial prefix of depth 11 and code 70284 returns the complete row with depth 11, base-four code 70284, original node 900903, kind 2, reserved field 0, 1517 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34657", "selected_cut_34657", "Selected cut at depth 12, code 281359, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 281359 returns the complete row with depth 12, base-four code 281359, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-17570-900808", "unmarked_context_10_17570_900808", "Unmarked parent at depth 10, code 17570",
                "The frontier Boolean is false at remaining fuel 11, original node 900808, the whole prefixCache at depth 10 and code 17570, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-17584-903808", "unmarked_context_10_17584_903808", "Unmarked parent at depth 10, code 17584",
                "The frontier Boolean is false at remaining fuel 11, original node 903808, the whole prefixCache at depth 10 and code 17584, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-17570-900808", "node_context_10_17570_900808", "Original split at fuel 11 and node 900808",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 900363, 900586, 900587, 900807. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-17584-903808", "node_context_10_17584_903808", "Original split at fuel 11 and node 903808",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 903139, 903414, 903685, 903807. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-17570-900808", "context_10_17570_900808", "Context at depth 10, code 17570, node 900808",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 17570 and original node 900808, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_70280_900363, context_11_70281_900586, context_11_70282_900587, context_11_70283_900807.", DescribeRole.Theorem),
            Node("context-10-17584-903808", "context_10_17584_903808", "Context at depth 10, code 17584, node 903808",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 17584 and original node 903808, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_70336_903139, context_11_70337_903414, context_11_70338_903685, context_11_70339_903807.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
