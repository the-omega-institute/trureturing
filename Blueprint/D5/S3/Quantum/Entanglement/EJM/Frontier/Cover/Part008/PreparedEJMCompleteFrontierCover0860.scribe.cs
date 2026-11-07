using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0860Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0860.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0860",
        H("Original frontier context coverage 0860"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41283", "selected_cut_41283", "Selected cut at depth 12, code 334617, node 1128678",
                "At remaining fuel 9 and original index 1128678, selection on the full partial prefix of depth 12 and code 334617 returns the complete row with depth 12, base-four code 334617, original node 1128678, kind 2, reserved field 0, 2841 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41330", "selected_cut_41330", "Selected cut at depth 12, code 334667, node 1130319",
                "At remaining fuel 9 and original index 1130319, selection on the full partial prefix of depth 12 and code 334667 returns the complete row with depth 12, base-four code 334667, original node 1130319, kind 2, reserved field 0, 2273 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83654-1128796", "unmarked_context_11_83654_1128796", "Unmarked parent at depth 11, code 83654",
                "The frontier Boolean is false at remaining fuel 10, original node 1128796, the whole prefixCache at depth 11 and code 83654, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-83666-1130320", "unmarked_context_11_83666_1130320", "Unmarked parent at depth 11, code 83666",
                "The frontier Boolean is false at remaining fuel 10, original node 1130320, the whole prefixCache at depth 11 and code 83666, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83654-1128796", "node_context_11_83654_1128796", "Original split at fuel 10 and node 1128796",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1128678, 1128728, 1128795. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-83666-1130320", "node_context_11_83666_1130320", "Original split at fuel 10 and node 1130320",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1130229, 1130257, 1130285, 1130319. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-334617-1128678", "context_12_334617_1128678", "Context at depth 12, code 334617, node 1128678",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 334617 and original node 1128678, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-83666-1130320", "context_11_83666_1130320", "Context at depth 11, code 83666, node 1130320",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 83666 and original node 1130320, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_334664_1130229, context_12_334665_1130257, context_12_334666_1130285, context_12_334667_1130319.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
