using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0718Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0718.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0718",
        H("Original frontier context coverage 0718"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34466", "selected_cut_34466", "Selected cut at depth 12, code 280070, node 893814",
                "At remaining fuel 9 and original index 893814, selection on the full partial prefix of depth 12 and code 280070 returns the complete row with depth 12, base-four code 280070, original node 893814, kind 2, reserved field 0, 3249 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34514", "selected_cut_34514", "Selected cut at depth 12, code 280127, node 896639",
                "At remaining fuel 9 and original index 896639, selection on the full partial prefix of depth 12 and code 280127 returns the complete row with depth 12, base-four code 280127, original node 896639, kind 2, reserved field 0, 2137 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-70017-893902", "unmarked_context_11_70017_893902", "Unmarked parent at depth 11, code 70017",
                "The frontier Boolean is false at remaining fuel 10, original node 893902, the whole prefixCache at depth 11 and code 70017, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-70031-896640", "unmarked_context_11_70031_896640", "Unmarked parent at depth 11, code 70031",
                "The frontier Boolean is false at remaining fuel 10, original node 896640, the whole prefixCache at depth 11 and code 70031, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-70017-893902", "node_context_11_70017_893902", "Original split at fuel 10 and node 893902",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 895, 893744, 893814, 893901. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-70031-896640", "node_context_11_70031_896640", "Original split at fuel 10 and node 896640",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 896527, 896561, 896602, 896639. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-280070-893814", "context_12_280070_893814", "Context at depth 12, code 280070, node 893814",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 280070 and original node 893814, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-70031-896640", "context_11_70031_896640", "Context at depth 11, code 70031, node 896640",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 70031 and original node 896640, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_280124_896527, context_12_280125_896561, context_12_280126_896602, context_12_280127_896639.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
