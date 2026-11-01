using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0871Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0871.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0871",
        H("Original frontier context coverage 0871"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41811", "selected_cut_41811", "Selected cut at depth 12, code 336714, node 1143061",
                "At remaining fuel 9 and original index 1143061, selection on the full partial prefix of depth 12 and code 336714 returns the complete row with depth 12, base-four code 336714, original node 1143061, kind 2, reserved field 0, 1781 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41858", "selected_cut_41858", "Selected cut at depth 12, code 336785, node 1144083",
                "At remaining fuel 9 and original index 1144083, selection on the full partial prefix of depth 12 and code 336785 returns the complete row with depth 12, base-four code 336785, original node 1144083, kind 2, reserved field 0, 1273 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84178-1143099", "unmarked_context_11_84178_1143099", "Unmarked parent at depth 11, code 84178",
                "The frontier Boolean is false at remaining fuel 10, original node 1143099, the whole prefixCache at depth 11 and code 84178, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21048-1144038", "unmarked_context_10_21048_1144038", "Unmarked parent at depth 10, code 21048",
                "The frontier Boolean is false at remaining fuel 11, original node 1144038, the whole prefixCache at depth 10 and code 21048, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84178-1143099", "node_context_11_84178_1143099", "Original split at fuel 10 and node 1143099",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1142992, 1143030, 1143061, 1143098. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21048-1144038", "node_context_10_21048_1144038", "Original split at fuel 11 and node 1144038",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 1143933, 1143994, 1144037. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-336714-1143061", "context_12_336714_1143061", "Context at depth 12, code 336714, node 1143061",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336714 and original node 1143061, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-336785-1144083", "context_12_336785_1144083", "Context at depth 12, code 336785, node 1144083",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336785 and original node 1144083, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
