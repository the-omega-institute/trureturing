using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0685Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0685.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0685",
        H("Original frontier context coverage 0685"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32884", "selected_cut_32884", "Selected cut at depth 13, code 439414, node 846773",
                "At remaining fuel 8 and original index 846773, selection on the full partial prefix of depth 13 and code 439414 returns the complete row with depth 13, base-four code 439414, original node 846773, kind 2, reserved field 0, 1477 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32931", "selected_cut_32931", "Selected cut at depth 13, code 439461, node 848004",
                "At remaining fuel 8 and original index 848004, selection on the full partial prefix of depth 13 and code 439461 returns the complete row with depth 13, base-four code 439461, original node 848004, kind 2, reserved field 0, 2253 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-109853-846781", "unmarked_context_12_109853_846781", "Unmarked parent at depth 12, code 109853",
                "The frontier Boolean is false at remaining fuel 9, original node 846781, the whole prefixCache at depth 12 and code 109853, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-109864-847967", "unmarked_context_12_109864_847967", "Unmarked parent at depth 12, code 109864",
                "The frontier Boolean is false at remaining fuel 9, original node 847967, the whole prefixCache at depth 12 and code 109864, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-109853-846781", "node_context_12_109853_846781", "Original split at fuel 9 and node 846781",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 846712, 846746, 846773, 846780. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-109864-847967", "node_context_12_109864_847967", "Original split at fuel 9 and node 847967",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 847907, 847934, 847961, 847966. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-439414-846773", "context_13_439414_846773", "Context at depth 13, code 439414, node 846773",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 439414 and original node 846773, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-439461-848004", "context_13_439461_848004", "Context at depth 13, code 439461, node 848004",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 439461 and original node 848004, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
