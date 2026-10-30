using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1070Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1070.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1070",
        H("Original frontier context coverage 1070"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51363", "selected_cut_51363", "Selected cut at depth 10, code 70200, node 1480510",
                "At remaining fuel 11 and original index 1480510, selection on the full partial prefix of depth 10 and code 70200 returns the complete row with depth 10, base-four code 70200, original node 1480510, kind 2, reserved field 0, 2213 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51410", "selected_cut_51410", "Selected cut at depth 11, code 280988, node 1482400",
                "At remaining fuel 10 and original index 1482400, selection on the full partial prefix of depth 11 and code 280988 returns the complete row with depth 11, base-four code 280988, original node 1482400, kind 2, reserved field 0, 1613 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-17549-1480454", "unmarked_context_9_17549_1480454", "Unmarked parent at depth 9, code 17549",
                "The frontier Boolean is false at remaining fuel 12, original node 1480454, the whole prefixCache at depth 9 and code 17549, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-70246-1482372", "unmarked_context_10_70246_1482372", "Unmarked parent at depth 10, code 70246",
                "The frontier Boolean is false at remaining fuel 11, original node 1482372, the whole prefixCache at depth 10 and code 70246, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-17549-1480454", "node_context_9_17549_1480454", "Original split at fuel 12 and node 1480454",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1480216, 1468874, 1480343, 1480453. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-70246-1482372", "node_context_10_70246_1482372", "Original split at fuel 11 and node 1482372",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1482287, 1482334, 1468743, 1482371. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-17549-1480454", "context_9_17549_1480454", "Context at depth 9, code 17549, node 1480454",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 17549 and original node 1480454, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_70196_1480216, context_10_70197_1468874, context_10_70198_1480343, context_10_70199_1480453.", DescribeRole.Theorem),
            Node("context-11-280988-1482400", "context_11_280988_1482400", "Context at depth 11, code 280988, node 1482400",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 280988 and original node 1482400, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
