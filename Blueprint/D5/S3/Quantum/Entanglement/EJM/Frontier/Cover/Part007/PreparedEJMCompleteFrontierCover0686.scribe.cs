using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0686Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0686.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0686",
        H("Original frontier context coverage 0686"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32932", "selected_cut_32932", "Selected cut at depth 13, code 439462, node 848031",
                "At remaining fuel 8 and original index 848031, selection on the full partial prefix of depth 13 and code 439462 returns the complete row with depth 13, base-four code 439462, original node 848031, kind 2, reserved field 0, 1545 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32979", "selected_cut_32979", "Selected cut at depth 12, code 109878, node 848900",
                "At remaining fuel 9 and original index 848900, selection on the full partial prefix of depth 12 and code 109878 returns the complete row with depth 12, base-four code 109878, original node 848900, kind 2, reserved field 0, 3725 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-109865-848041", "unmarked_context_12_109865_848041", "Unmarked parent at depth 12, code 109865",
                "The frontier Boolean is false at remaining fuel 9, original node 848041, the whole prefixCache at depth 12 and code 109865, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-109876-848851", "unmarked_context_12_109876_848851", "Unmarked parent at depth 12, code 109876",
                "The frontier Boolean is false at remaining fuel 9, original node 848851, the whole prefixCache at depth 12 and code 109876, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-109865-848041", "node_context_12_109865_848041", "Original split at fuel 9 and node 848041",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 847980, 848004, 848031, 848040. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-109876-848851", "node_context_12_109876_848851", "Original split at fuel 9 and node 848851",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 848798, 848825, 848844, 848850. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-439462-848031", "context_13_439462_848031", "Context at depth 13, code 439462, node 848031",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 439462 and original node 848031, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-109878-848900", "context_12_109878_848900", "Context at depth 12, code 109878, node 848900",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109878 and original node 848900, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
