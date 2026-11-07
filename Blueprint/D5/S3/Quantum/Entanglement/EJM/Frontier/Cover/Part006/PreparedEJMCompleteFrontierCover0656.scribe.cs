using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0656Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0656.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0656",
        H("Original frontier context coverage 0656"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31492", "selected_cut_31492", "Selected cut at depth 13, code 424102, node 808495",
                "At remaining fuel 8 and original index 808495, selection on the full partial prefix of depth 13 and code 424102 returns the complete row with depth 13, base-four code 424102, original node 808495, kind 2, reserved field 0, 1513 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31539", "selected_cut_31539", "Selected cut at depth 13, code 424152, node 809480",
                "At remaining fuel 8 and original index 809480, selection on the full partial prefix of depth 13 and code 424152 returns the complete row with depth 13, base-four code 424152, original node 809480, kind 2, reserved field 0, 317 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-106025-808505", "unmarked_context_12_106025_808505", "Unmarked parent at depth 12, code 106025",
                "The frontier Boolean is false at remaining fuel 9, original node 808505, the whole prefixCache at depth 12 and code 106025, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-106037-809473", "unmarked_context_12_106037_809473", "Unmarked parent at depth 12, code 106037",
                "The frontier Boolean is false at remaining fuel 9, original node 809473, the whole prefixCache at depth 12 and code 106037, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-106025-808505", "node_context_12_106025_808505", "Original split at fuel 9 and node 808505",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 808426, 808471, 808495, 808504. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-106037-809473", "node_context_12_106037_809473", "Original split at fuel 9 and node 809473",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 809395, 809436, 809462, 809472. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-424102-808495", "context_13_424102_808495", "Context at depth 13, code 424102, node 808495",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424102 and original node 808495, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-424152-809480", "context_13_424152_809480", "Context at depth 13, code 424152, node 809480",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424152 and original node 809480, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
