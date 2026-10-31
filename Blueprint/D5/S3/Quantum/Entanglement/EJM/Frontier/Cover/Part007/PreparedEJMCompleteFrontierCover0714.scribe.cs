using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0714Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0714.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0714",
        H("Original frontier context coverage 0714"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34276", "selected_cut_34276", "Selected cut at depth 13, code 452695, node 886011",
                "At remaining fuel 8 and original index 886011, selection on the full partial prefix of depth 13 and code 452695 returns the complete row with depth 13, base-four code 452695, original node 886011, kind 2, reserved field 0, 1105 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34323", "selected_cut_34323", "Selected cut at depth 13, code 452748, node 887368",
                "At remaining fuel 8 and original index 887368, selection on the full partial prefix of depth 13 and code 452748 returns the complete row with depth 13, base-four code 452748, original node 887368, kind 2, reserved field 0, 1061 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-113173-886012", "unmarked_context_12_113173_886012", "Unmarked parent at depth 12, code 113173",
                "The frontier Boolean is false at remaining fuel 9, original node 886012, the whole prefixCache at depth 12 and code 113173, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-113185-887242", "unmarked_context_12_113185_887242", "Unmarked parent at depth 12, code 113185",
                "The frontier Boolean is false at remaining fuel 9, original node 887242, the whole prefixCache at depth 12 and code 113185, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-113173-886012", "node_context_12_113173_886012", "Original split at fuel 9 and node 886012",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 885937, 885965, 885987, 886011. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-113185-887242", "node_context_12_113185_887242", "Original split at fuel 9 and node 887242",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 887142, 887207, 887233, 887241. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-452695-886011", "context_13_452695_886011", "Context at depth 13, code 452695, node 886011",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 452695 and original node 886011, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-452748-887368", "context_13_452748_887368", "Context at depth 13, code 452748, node 887368",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 452748 and original node 887368, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
