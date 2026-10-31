using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0329Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0329.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0329",
        H("Original frontier context coverage 0329"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15796", "selected_cut_15796", "Selected cut at depth 13, code 111799, node 404264",
                "At remaining fuel 8 and original index 404264, selection on the full partial prefix of depth 13 and code 111799 returns the complete row with depth 13, base-four code 111799, original node 404264, kind 2, reserved field 0, 1053 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15843", "selected_cut_15843", "Selected cut at depth 13, code 111846, node 405130",
                "At remaining fuel 8 and original index 405130, selection on the full partial prefix of depth 13 and code 111846 returns the complete row with depth 13, base-four code 111846, original node 405130, kind 2, reserved field 0, 1689 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27949-404265", "unmarked_context_12_27949_404265", "Unmarked parent at depth 12, code 27949",
                "The frontier Boolean is false at remaining fuel 9, original node 404265, the whole prefixCache at depth 12 and code 27949, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27960-405081", "unmarked_context_12_27960_405081", "Unmarked parent at depth 12, code 27960",
                "The frontier Boolean is false at remaining fuel 9, original node 405081, the whole prefixCache at depth 12 and code 27960, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27949-404265", "node_context_12_27949_404265", "Original split at fuel 9 and node 404265",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 404213, 404236, 404257, 404264. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27960-405081", "node_context_12_27960_405081", "Original split at fuel 9 and node 405081",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 405025, 405055, 405075, 405080. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-111799-404264", "context_13_111799_404264", "Context at depth 13, code 111799, node 404264",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111799 and original node 404264, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-111846-405130", "context_13_111846_405130", "Context at depth 13, code 111846, node 405130",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111846 and original node 405130, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
