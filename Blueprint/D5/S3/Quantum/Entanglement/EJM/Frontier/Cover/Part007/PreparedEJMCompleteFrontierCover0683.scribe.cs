using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0683Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0683.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0683",
        H("Original frontier context coverage 0683"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32787", "selected_cut_32787", "Selected cut at depth 11, code 27432, node 844336",
                "At remaining fuel 10 and original index 844336, selection on the full partial prefix of depth 11 and code 27432 returns the complete row with depth 11, base-four code 27432, original node 844336, kind 2, reserved field 0, 3181 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32834", "selected_cut_32834", "Selected cut at depth 13, code 439361, node 845532",
                "At remaining fuel 8 and original index 845532, selection on the full partial prefix of depth 13 and code 439361 returns the complete row with depth 13, base-four code 439361, original node 845532, kind 2, reserved field 0, 2301 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-27433-844393", "unmarked_context_11_27433_844393", "Unmarked parent at depth 11, code 27433",
                "The frontier Boolean is false at remaining fuel 10, original node 844393, the whole prefixCache at depth 11 and code 27433, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6864-845481", "unmarked_context_10_6864_845481", "Unmarked parent at depth 10, code 6864",
                "The frontier Boolean is false at remaining fuel 11, original node 845481, the whole prefixCache at depth 10 and code 6864, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-27433-844393", "node_context_11_27433_844393", "Original split at fuel 10 and node 844393",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 844356, 844370, 769937, 844392. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6864-845481", "node_context_10_6864_845481", "Original split at fuel 11 and node 845481",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 845216, 845480, 789341. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-27432-844336", "context_11_27432_844336", "Context at depth 11, code 27432, node 844336",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27432 and original node 844336, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-439361-845532", "context_13_439361_845532", "Context at depth 13, code 439361, node 845532",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 439361 and original node 845532, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
