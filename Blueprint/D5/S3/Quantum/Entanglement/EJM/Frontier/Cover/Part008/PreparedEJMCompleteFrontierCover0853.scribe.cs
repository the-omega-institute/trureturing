using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0853Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0853.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0853",
        H("Original frontier context coverage 0853"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40948", "selected_cut_40948", "Selected cut at depth 12, code 333424, node 1117246",
                "At remaining fuel 9 and original index 1117246, selection on the full partial prefix of depth 12 and code 333424 returns the complete row with depth 12, base-four code 333424, original node 1117246, kind 2, reserved field 0, 1449 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40993", "selected_cut_40993", "Selected cut at depth 12, code 333832, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 333832 returns the complete row with depth 12, base-four code 333832, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83355-1117224", "unmarked_context_11_83355_1117224", "Unmarked parent at depth 11, code 83355",
                "The frontier Boolean is false at remaining fuel 10, original node 1117224, the whole prefixCache at depth 11 and code 83355, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-83457-1118508", "unmarked_context_11_83457_1118508", "Unmarked parent at depth 11, code 83457",
                "The frontier Boolean is false at remaining fuel 10, original node 1118508, the whole prefixCache at depth 11 and code 83457, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83355-1117224", "node_context_11_83355_1117224", "Original split at fuel 10 and node 1117224",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1117134, 1117157, 1117191, 1117223. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-83457-1118508", "node_context_11_83457_1118508", "Original split at fuel 10 and node 1118508",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1118392, 1118451, 1118507. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-83355-1117224", "context_11_83355_1117224", "Context at depth 11, code 83355, node 1117224",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 83355 and original node 1117224, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_333420_1117134, context_12_333421_1117157, context_12_333422_1117191, context_12_333423_1117223.", DescribeRole.Theorem),
            Node("context-12-333832-448748", "context_12_333832_448748", "Context at depth 12, code 333832, node 448748",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 333832 and original node 448748, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
