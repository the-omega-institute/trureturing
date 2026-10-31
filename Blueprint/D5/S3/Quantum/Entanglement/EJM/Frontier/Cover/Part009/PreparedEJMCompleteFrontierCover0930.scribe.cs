using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0930Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0930.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0930",
        H("Original frontier context coverage 0930"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44643", "selected_cut_44643", "Selected cut at depth 11, code 88665, node 1229238",
                "At remaining fuel 10 and original index 1229238, selection on the full partial prefix of depth 11 and code 88665 returns the complete row with depth 11, base-four code 88665, original node 1229238, kind 2, reserved field 0, 3117 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44691", "selected_cut_44691", "Selected cut at depth 12, code 354843, node 1230981",
                "At remaining fuel 9 and original index 1230981, selection on the full partial prefix of depth 12 and code 354843 returns the complete row with depth 12, base-four code 354843, original node 1230981, kind 2, reserved field 0, 3333 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22166-1229294", "unmarked_context_10_22166_1229294", "Unmarked parent at depth 10, code 22166",
                "The frontier Boolean is false at remaining fuel 11, original node 1229294, the whole prefixCache at depth 10 and code 22166, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88708-1230758", "unmarked_context_11_88708_1230758", "Unmarked parent at depth 11, code 88708",
                "The frontier Boolean is false at remaining fuel 10, original node 1230758, the whole prefixCache at depth 11 and code 88708, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22166-1229294", "node_context_10_22166_1229294", "Original split at fuel 11 and node 1229294",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1229181, 1229238, 900587, 1229293. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88708-1230758", "node_context_11_88708_1230758", "Original split at fuel 10 and node 1230758",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 1230627, 1230685, 1230757. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-88665-1229238", "context_11_88665_1229238", "Context at depth 11, code 88665, node 1229238",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88665 and original node 1229238, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-354843-1230981", "context_12_354843_1230981", "Context at depth 12, code 354843, node 1230981",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 354843 and original node 1230981, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
