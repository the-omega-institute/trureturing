using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0491Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0491.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0491",
        H("Original frontier context coverage 0491"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23571", "selected_cut_23571", "Selected cut at depth 13, code 306264, node 596654",
                "At remaining fuel 8 and original index 596654, selection on the full partial prefix of depth 13 and code 306264 returns the complete row with depth 13, base-four code 306264, original node 596654, kind 2, reserved field 0, 2029 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23619", "selected_cut_23619", "Selected cut at depth 13, code 306315, node 597762",
                "At remaining fuel 8 and original index 597762, selection on the full partial prefix of depth 13 and code 306315 returns the complete row with depth 13, base-four code 306315, original node 597762, kind 2, reserved field 0, 601 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76566-596715", "unmarked_context_12_76566_596715", "Unmarked parent at depth 12, code 76566",
                "The frontier Boolean is false at remaining fuel 9, original node 596715, the whole prefixCache at depth 12 and code 76566, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76577-597699", "unmarked_context_12_76577_597699", "Unmarked parent at depth 12, code 76577",
                "The frontier Boolean is false at remaining fuel 9, original node 597699, the whole prefixCache at depth 12 and code 76577, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76566-596715", "node_context_12_76566_596715", "Original split at fuel 9 and node 596715",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 596654, 596684, 596705, 596714. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76577-597699", "node_context_12_76577_597699", "Original split at fuel 9 and node 597699",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 597649, 597674, 597693, 597698. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-306264-596654", "context_13_306264_596654", "Context at depth 13, code 306264, node 596654",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 306264 and original node 596654, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-306315-597762", "context_13_306315_597762", "Context at depth 13, code 306315, node 597762",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 306315 and original node 597762, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
