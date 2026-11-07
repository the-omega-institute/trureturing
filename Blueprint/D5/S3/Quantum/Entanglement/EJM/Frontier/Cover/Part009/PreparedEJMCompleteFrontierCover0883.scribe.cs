using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0883Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0883.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0883",
        H("Original frontier context coverage 0883"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42387", "selected_cut_42387", "Selected cut at depth 12, code 337932, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 337932 returns the complete row with depth 12, base-four code 337932, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42435", "selected_cut_42435", "Selected cut at depth 12, code 337983, node 1120582",
                "At remaining fuel 9 and original index 1120582, selection on the full partial prefix of depth 12 and code 337983 returns the complete row with depth 12, base-four code 337983, original node 1120582, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84482-1158352", "unmarked_context_11_84482_1158352", "Unmarked parent at depth 11, code 84482",
                "The frontier Boolean is false at remaining fuel 10, original node 1158352, the whole prefixCache at depth 11 and code 84482, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84494-1159750", "unmarked_context_11_84494_1159750", "Unmarked parent at depth 11, code 84494",
                "The frontier Boolean is false at remaining fuel 10, original node 1159750, the whole prefixCache at depth 11 and code 84494, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84482-1158352", "node_context_11_84482_1158352", "Original split at fuel 10 and node 1158352",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1158313, 188189, 1158351. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84494-1159750", "node_context_11_84494_1159750", "Original split at fuel 10 and node 1159750",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1159669, 1159702, 1159749. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84482-1158352", "context_11_84482_1158352", "Context at depth 11, code 84482, node 1158352",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84482 and original node 1158352, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_337928_448748, context_12_337929_1158313, context_12_337930_188189, context_12_337931_1158351.", DescribeRole.Theorem),
            Node("context-12-337983-1120582", "context_12_337983_1120582", "Context at depth 12, code 337983, node 1120582",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 337983 and original node 1120582, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
