using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0495Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0495.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0495",
        H("Original frontier context coverage 0495"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23763", "selected_cut_23763", "Selected cut at depth 13, code 306516, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 306516 returns the complete row with depth 13, base-four code 306516, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23812", "selected_cut_23812", "Selected cut at depth 13, code 306607, node 601328",
                "At remaining fuel 8 and original index 601328, selection on the full partial prefix of depth 13 and code 306607 returns the complete row with depth 13, base-four code 306607, original node 601328, kind 2, reserved field 0, 1109 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76629-600246", "unmarked_context_12_76629_600246", "Unmarked parent at depth 12, code 76629",
                "The frontier Boolean is false at remaining fuel 9, original node 600246, the whole prefixCache at depth 12 and code 76629, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76649-601275", "unmarked_context_12_76649_601275", "Unmarked parent at depth 12, code 76649",
                "The frontier Boolean is false at remaining fuel 9, original node 601275, the whole prefixCache at depth 12 and code 76649, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76629-600246", "node_context_12_76629_600246", "Original split at fuel 9 and node 600246",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 600224, 600239, 600245. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76649-601275", "node_context_12_76649_601275", "Original split at fuel 9 and node 601275",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 601237, 601260, 601274. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-306516-3444", "context_13_306516_3444", "Context at depth 13, code 306516, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 306516 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-306607-601328", "context_13_306607_601328", "Context at depth 13, code 306607, node 601328",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 306607 and original node 601328, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
