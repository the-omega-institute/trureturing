using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0498Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0498.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0498",
        H("Original frontier context coverage 0498"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23907", "selected_cut_23907", "Selected cut at depth 11, code 19200, node 434745",
                "At remaining fuel 10 and original index 434745, selection on the full partial prefix of depth 11 and code 19200 returns the complete row with depth 11, base-four code 19200, original node 434745, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23955", "selected_cut_23955", "Selected cut at depth 13, code 307311, node 605336",
                "At remaining fuel 8 and original index 605336, selection on the full partial prefix of depth 13 and code 307311 returns the complete row with depth 13, base-four code 307311, original node 605336, kind 2, reserved field 0, 881 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-8-299-603600", "unmarked_context_8_299_603600", "Unmarked parent at depth 8, code 299",
                "The frontier Boolean is false at remaining fuel 13, original node 603600, the whole prefixCache at depth 8 and code 299, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76826-605206", "unmarked_context_12_76826_605206", "Unmarked parent at depth 12, code 76826",
                "The frontier Boolean is false at remaining fuel 9, original node 605206, the whole prefixCache at depth 12 and code 76826, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-8-299-603600", "node_context_8_299_603600", "Original split at fuel 13 and node 603600",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 599138, 602107, 603312, 603599. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76826-605206", "node_context_12_76826_605206", "Original split at fuel 9 and node 605206",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 605137, 605170, 605191, 605205. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-8-299-603600", "context_8_299_603600", "Context at depth 8, code 299, node 603600",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 299 and original node 603600, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_9_1196_599138, context_9_1197_602107, context_9_1198_603312, context_9_1199_603599.", DescribeRole.Theorem),
            Node("context-13-307311-605336", "context_13_307311_605336", "Context at depth 13, code 307311, node 605336",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 307311 and original node 605336, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
