using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0914Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0914.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0914",
        H("Original frontier context coverage 0914"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43875", "selected_cut_43875", "Selected cut at depth 10, code 22047, node 1203343",
                "At remaining fuel 11 and original index 1203343, selection on the full partial prefix of depth 10 and code 22047 returns the complete row with depth 10, base-four code 22047, original node 1203343, kind 2, reserved field 0, 477 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43922", "selected_cut_43922", "Selected cut at depth 12, code 352823, node 1205062",
                "At remaining fuel 9 and original index 1205062, selection on the full partial prefix of depth 12 and code 352823 returns the complete row with depth 12, base-four code 352823, original node 1205062, kind 2, reserved field 0, 2417 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-5511-1203344", "unmarked_context_9_5511_1203344", "Unmarked parent at depth 9, code 5511",
                "The frontier Boolean is false at remaining fuel 12, original node 1203344, the whole prefixCache at depth 9 and code 5511, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88205-1205063", "unmarked_context_11_88205_1205063", "Unmarked parent at depth 11, code 88205",
                "The frontier Boolean is false at remaining fuel 10, original node 1205063, the whole prefixCache at depth 11 and code 88205, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-5511-1203344", "node_context_9_5511_1203344", "Original split at fuel 12 and node 1203344",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1203232, 1203283, 1203331, 1203343. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88205-1205063", "node_context_11_88205_1205063", "Original split at fuel 10 and node 1205063",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1204952, 1204989, 1205018, 1205062. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-22047-1203343", "context_10_22047_1203343", "Context at depth 10, code 22047, node 1203343",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22047 and original node 1203343, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-88205-1205063", "context_11_88205_1205063", "Context at depth 11, code 88205, node 1205063",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88205 and original node 1205063, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_352820_1204952, context_12_352821_1204989, context_12_352822_1205018, context_12_352823_1205062.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
