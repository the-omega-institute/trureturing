using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0619Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0619.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0619",
        H("Original frontier context coverage 0619"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29716", "selected_cut_29716", "Selected cut at depth 13, code 374968, node 749861",
                "At remaining fuel 8 and original index 749861, selection on the full partial prefix of depth 13 and code 374968 returns the complete row with depth 13, base-four code 374968, original node 749861, kind 2, reserved field 0, 573 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29764", "selected_cut_29764", "Selected cut at depth 13, code 375022, node 750781",
                "At remaining fuel 8 and original index 750781, selection on the full partial prefix of depth 13 and code 375022 returns the complete row with depth 13, base-four code 375022, original node 750781, kind 2, reserved field 0, 1829 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93742-749913", "unmarked_context_12_93742_749913", "Unmarked parent at depth 12, code 93742",
                "The frontier Boolean is false at remaining fuel 9, original node 749913, the whole prefixCache at depth 12 and code 93742, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93753-750593", "unmarked_context_12_93753_750593", "Unmarked parent at depth 12, code 93753",
                "The frontier Boolean is false at remaining fuel 9, original node 750593, the whole prefixCache at depth 12 and code 93753, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93742-749913", "node_context_12_93742_749913", "Original split at fuel 9 and node 749913",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 749861, 749888, 749902, 749912. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93753-750593", "node_context_12_93753_750593", "Original split at fuel 9 and node 750593",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 750540, 750565, 750581, 750592. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-374968-749861", "context_13_374968_749861", "Context at depth 13, code 374968, node 749861",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 374968 and original node 749861, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-375022-750781", "context_13_375022_750781", "Context at depth 13, code 375022, node 750781",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 375022 and original node 750781, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
