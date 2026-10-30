using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0566Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0566.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0566",
        H("Original frontier context coverage 0566"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27170", "selected_cut_27170", "Selected cut at depth 13, code 365636, node 687768",
                "At remaining fuel 8 and original index 687768, selection on the full partial prefix of depth 13 and code 365636 returns the complete row with depth 13, base-four code 365636, original node 687768, kind 2, reserved field 0, 1449 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27218", "selected_cut_27218", "Selected cut at depth 13, code 365702, node 688661",
                "At remaining fuel 8 and original index 688661, selection on the full partial prefix of depth 13 and code 365702 returns the complete row with depth 13, base-four code 365702, original node 688661, kind 2, reserved field 0, 1441 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91409-687813", "unmarked_context_12_91409_687813", "Unmarked parent at depth 12, code 91409",
                "The frontier Boolean is false at remaining fuel 9, original node 687813, the whole prefixCache at depth 12 and code 91409, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91424-688594", "unmarked_context_12_91424_688594", "Unmarked parent at depth 12, code 91424",
                "The frontier Boolean is false at remaining fuel 9, original node 688594, the whole prefixCache at depth 12 and code 91424, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91409-687813", "node_context_12_91409_687813", "Original split at fuel 9 and node 687813",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 687768, 687789, 687805, 687812. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91424-688594", "node_context_12_91424_688594", "Original split at fuel 9 and node 688594",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 688546, 688567, 688584, 688593. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-365636-687768", "context_13_365636_687768", "Context at depth 13, code 365636, node 687768",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 365636 and original node 687768, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-365702-688661", "context_13_365702_688661", "Context at depth 13, code 365702, node 688661",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 365702 and original node 688661, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
