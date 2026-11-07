using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0945Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0945.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0945",
        H("Original frontier context coverage 0945"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45363", "selected_cut_45363", "Selected cut at depth 11, code 91800, node 1256929",
                "At remaining fuel 10 and original index 1256929, selection on the full partial prefix of depth 11 and code 91800 returns the complete row with depth 11, base-four code 91800, original node 1256929, kind 2, reserved field 0, 1805 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45411", "selected_cut_45411", "Selected cut at depth 12, code 367407, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 367407 returns the complete row with depth 12, base-four code 367407, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22950-1257032", "unmarked_context_10_22950_1257032", "Unmarked parent at depth 10, code 22950",
                "The frontier Boolean is false at remaining fuel 11, original node 1257032, the whole prefixCache at depth 10 and code 22950, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-91851-1258999", "unmarked_context_11_91851_1258999", "Unmarked parent at depth 11, code 91851",
                "The frontier Boolean is false at remaining fuel 10, original node 1258999, the whole prefixCache at depth 11 and code 91851, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22950-1257032", "node_context_10_22950_1257032", "Original split at fuel 11 and node 1257032",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1256929, 1256992, 900587, 1257031. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-91851-1258999", "node_context_11_91851_1258999", "Original split at fuel 10 and node 1258999",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1258929, 1258961, 1258998, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-91800-1256929", "context_11_91800_1256929", "Context at depth 11, code 91800, node 1256929",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 91800 and original node 1256929, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-91851-1258999", "context_11_91851_1258999", "Context at depth 11, code 91851, node 1258999",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 91851 and original node 1258999, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_367404_1258929, context_12_367405_1258961, context_12_367406_1258998, context_12_367407_903806.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
