using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1053Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1053.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1053",
        H("Original frontier context coverage 1053"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50548", "selected_cut_50548", "Selected cut at depth 11, code 106384, node 1445340",
                "At remaining fuel 10 and original index 1445340, selection on the full partial prefix of depth 11 and code 106384 returns the complete row with depth 11, base-four code 106384, original node 1445340, kind 2, reserved field 0, 1349 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50596", "selected_cut_50596", "Selected cut at depth 12, code 425779, node 1447208",
                "At remaining fuel 9 and original index 1447208, selection on the full partial prefix of depth 12 and code 425779 returns the complete row with depth 12, base-four code 425779, original node 1447208, kind 2, reserved field 0, 1365 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-6648-1445306", "unmarked_context_9_6648_1445306", "Unmarked parent at depth 9, code 6648",
                "The frontier Boolean is false at remaining fuel 12, original node 1445306, the whole prefixCache at depth 9 and code 6648, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-26610-1447100", "unmarked_context_10_26610_1447100", "Unmarked parent at depth 10, code 26610",
                "The frontier Boolean is false at remaining fuel 11, original node 1447100, the whole prefixCache at depth 10 and code 26610, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-6648-1445306", "node_context_9_6648_1445306", "Original split at fuel 12 and node 1445306",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1444361, 1444745, 1445073, 1445305. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-26610-1447100", "node_context_10_26610_1447100", "Original split at fuel 11 and node 1447100",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1446890, 1446965, 1446966, 1447099. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-6648-1445306", "context_9_6648_1445306", "Context at depth 9, code 6648, node 1445306",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 6648 and original node 1445306, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_26592_1444361, context_10_26593_1444745, context_10_26594_1445073, context_10_26595_1445305.", DescribeRole.Theorem),
            Node("context-12-425779-1447208", "context_12_425779_1447208", "Context at depth 12, code 425779, node 1447208",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 425779 and original node 1447208, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
