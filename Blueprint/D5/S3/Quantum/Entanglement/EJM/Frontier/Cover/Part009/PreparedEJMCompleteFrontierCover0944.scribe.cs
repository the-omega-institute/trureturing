using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0944Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0944.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0944",
        H("Original frontier context coverage 0944"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45315", "selected_cut_45315", "Selected cut at depth 12, code 367110, node 1254693",
                "At remaining fuel 9 and original index 1254693, selection on the full partial prefix of depth 12 and code 367110 returns the complete row with depth 12, base-four code 367110, original node 1254693, kind 2, reserved field 0, 3829 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45362", "selected_cut_45362", "Selected cut at depth 10, code 22949, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 22949 returns the complete row with depth 10, base-four code 22949, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-367111-1254811", "unmarked_context_12_367111_1254811", "Unmarked parent at depth 12, code 367111",
                "The frontier Boolean is false at remaining fuel 9, original node 1254811, the whole prefixCache at depth 12 and code 367111, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5736-1256865", "unmarked_context_9_5736_1256865", "Unmarked parent at depth 9, code 5736",
                "The frontier Boolean is false at remaining fuel 12, original node 1256865, the whole prefixCache at depth 9 and code 5736, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-367111-1254811", "node_context_12_367111_1254811", "Original split at fuel 9 and node 1254811",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1254744, 1254774, 1254795, 1254810. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5736-1256865", "node_context_9_5736_1256865", "Original split at fuel 12 and node 1256865",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1255010, 1255841, 1256275, 1256864. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-367110-1254693", "context_12_367110_1254693", "Context at depth 12, code 367110, node 1254693",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 367110 and original node 1254693, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-22949-893098", "context_10_22949_893098", "Context at depth 10, code 22949, node 893098",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22949 and original node 893098, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
