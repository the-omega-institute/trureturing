using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0924Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0924.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0924",
        H("Original frontier context coverage 0924"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44355", "selected_cut_44355", "Selected cut at depth 12, code 353889, node 896706",
                "At remaining fuel 9 and original index 896706, selection on the full partial prefix of depth 12 and code 353889 returns the complete row with depth 12, base-four code 353889, original node 896706, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44403", "selected_cut_44403", "Selected cut at depth 12, code 354078, node 1221581",
                "At remaining fuel 9 and original index 1221581, selection on the full partial prefix of depth 12 and code 354078 returns the complete row with depth 12, base-four code 354078, original node 1221581, kind 2, reserved field 0, 2745 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88472-1219921", "unmarked_context_11_88472_1219921", "Unmarked parent at depth 11, code 88472",
                "The frontier Boolean is false at remaining fuel 10, original node 1219921, the whole prefixCache at depth 11 and code 88472, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88518-1221461", "unmarked_context_11_88518_1221461", "Unmarked parent at depth 11, code 88518",
                "The frontier Boolean is false at remaining fuel 10, original node 1221461, the whole prefixCache at depth 11 and code 88518, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88472-1219921", "node_context_11_88472_1219921", "Original split at fuel 10 and node 1219921",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1219884, 896706, 1219901, 1219920. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88518-1221461", "node_context_11_88518_1221461", "Original split at fuel 10 and node 1221461",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1221327, 1221364, 1221410, 1221460. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-353889-896706", "context_12_353889_896706", "Context at depth 12, code 353889, node 896706",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 353889 and original node 896706, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-354078-1221581", "context_12_354078_1221581", "Context at depth 12, code 354078, node 1221581",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 354078 and original node 1221581, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
