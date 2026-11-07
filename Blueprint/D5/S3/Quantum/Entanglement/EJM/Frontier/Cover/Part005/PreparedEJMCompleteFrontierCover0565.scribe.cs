using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0565Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0565.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0565",
        H("Original frontier context coverage 0565"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27123", "selected_cut_27123", "Selected cut at depth 11, code 22839, node 686239",
                "At remaining fuel 10 and original index 686239, selection on the full partial prefix of depth 11 and code 22839 returns the complete row with depth 11, base-four code 22839, original node 686239, kind 2, reserved field 0, 1873 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27169", "selected_cut_27169", "Selected cut at depth 13, code 365635, node 687745",
                "At remaining fuel 8 and original index 687745, selection on the full partial prefix of depth 13 and code 365635 returns the complete row with depth 13, base-four code 365635, original node 687745, kind 2, reserved field 0, 753 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-5709-686240", "unmarked_context_10_5709_686240", "Unmarked parent at depth 10, code 5709",
                "The frontier Boolean is false at remaining fuel 11, original node 686240, the whole prefixCache at depth 10 and code 5709, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91408-687746", "unmarked_context_12_91408_687746", "Unmarked parent at depth 12, code 91408",
                "The frontier Boolean is false at remaining fuel 9, original node 687746, the whole prefixCache at depth 12 and code 91408, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-5709-686240", "node_context_10_5709_686240", "Original split at fuel 11 and node 686240",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 686180, 686197, 686220, 686239. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91408-687746", "node_context_12_91408_687746", "Original split at fuel 9 and node 687746",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 687697, 687717, 687737, 687745. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-22839-686239", "context_11_22839_686239", "Context at depth 11, code 22839, node 686239",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 22839 and original node 686239, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-91408-687746", "context_12_91408_687746", "Context at depth 12, code 91408, node 687746",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91408 and original node 687746, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_365632_687697, context_13_365633_687717, context_13_365634_687737, context_13_365635_687745.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
