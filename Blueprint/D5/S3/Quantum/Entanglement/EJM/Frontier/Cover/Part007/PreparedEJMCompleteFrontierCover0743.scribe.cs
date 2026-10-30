using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0743Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0743.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0743",
        H("Original frontier context coverage 0743"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35666", "selected_cut_35666", "Selected cut at depth 12, code 287120, node 938874",
                "At remaining fuel 9 and original index 938874, selection on the full partial prefix of depth 12 and code 287120 returns the complete row with depth 12, base-four code 287120, original node 938874, kind 2, reserved field 0, 1177 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35714", "selected_cut_35714", "Selected cut at depth 13, code 1148978, node 940102",
                "At remaining fuel 8 and original index 940102, selection on the full partial prefix of depth 13 and code 1148978 returns the complete row with depth 13, base-four code 1148978, original node 940102, kind 2, reserved field 0, 1257 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71780-938914", "unmarked_context_11_71780_938914", "Unmarked parent at depth 11, code 71780",
                "The frontier Boolean is false at remaining fuel 10, original node 938914, the whole prefixCache at depth 11 and code 71780, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71810-940025", "unmarked_context_11_71810_940025", "Unmarked parent at depth 11, code 71810",
                "The frontier Boolean is false at remaining fuel 10, original node 940025, the whole prefixCache at depth 11 and code 71810, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71780-938914", "node_context_11_71780_938914", "Original split at fuel 10 and node 938914",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 938874, 938889, 938901, 938913. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71810-940025", "node_context_11_71810_940025", "Original split at fuel 10 and node 940025",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 939874, 939944, 893903, 940024. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-287120-938874", "context_12_287120_938874", "Context at depth 12, code 287120, node 938874",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287120 and original node 938874, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1148978-940102", "context_13_1148978_940102", "Context at depth 13, code 1148978, node 940102",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1148978 and original node 940102, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
