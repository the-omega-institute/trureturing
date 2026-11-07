using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0582Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0582.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0582",
        H("Original frontier context coverage 0582"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27940", "selected_cut_27940", "Selected cut at depth 13, code 367819, node 705657",
                "At remaining fuel 8 and original index 705657, selection on the full partial prefix of depth 13 and code 367819 returns the complete row with depth 13, base-four code 367819, original node 705657, kind 2, reserved field 0, 825 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27986", "selected_cut_27986", "Selected cut at depth 13, code 367880, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 367880 returns the complete row with depth 13, base-four code 367880, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91954-705658", "unmarked_context_12_91954_705658", "Unmarked parent at depth 12, code 91954",
                "The frontier Boolean is false at remaining fuel 9, original node 705658, the whole prefixCache at depth 12 and code 91954, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91968-706459", "unmarked_context_12_91968_706459", "Unmarked parent at depth 12, code 91968",
                "The frontier Boolean is false at remaining fuel 9, original node 706459, the whole prefixCache at depth 12 and code 91968, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91954-705658", "node_context_12_91954_705658", "Original split at fuel 9 and node 705658",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 705605, 705630, 705646, 705657. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91968-706459", "node_context_12_91968_706459", "Original split at fuel 9 and node 706459",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 706437, 706453, 706458. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-367819-705657", "context_13_367819_705657", "Context at depth 13, code 367819, node 705657",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 367819 and original node 705657, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-367880-3444", "context_13_367880_3444", "Context at depth 13, code 367880, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 367880 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
