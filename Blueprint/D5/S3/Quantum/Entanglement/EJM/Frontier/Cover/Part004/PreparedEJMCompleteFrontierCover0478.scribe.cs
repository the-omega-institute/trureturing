using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0478Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0478.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0478",
        H("Original frontier context coverage 0478"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22947", "selected_cut_22947", "Selected cut at depth 12, code 76074, node 474208",
                "At remaining fuel 9 and original index 474208, selection on the full partial prefix of depth 12 and code 76074 returns the complete row with depth 12, base-four code 76074, original node 474208, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22995", "selected_cut_22995", "Selected cut at depth 13, code 304350, node 582899",
                "At remaining fuel 8 and original index 582899, selection on the full partial prefix of depth 13 and code 304350 returns the complete row with depth 13, base-four code 304350, original node 582899, kind 2, reserved field 0, 1621 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76075-582175", "unmarked_context_12_76075_582175", "Unmarked parent at depth 12, code 76075",
                "The frontier Boolean is false at remaining fuel 9, original node 582175, the whole prefixCache at depth 12 and code 76075, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76086-582842", "unmarked_context_12_76086_582842", "Unmarked parent at depth 12, code 76086",
                "The frontier Boolean is false at remaining fuel 9, original node 582842, the whole prefixCache at depth 12 and code 76086, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76075-582175", "node_context_12_76075_582175", "Original split at fuel 9 and node 582175",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 582132, 582155, 582169, 582174. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76086-582842", "node_context_12_76086_582842", "Original split at fuel 9 and node 582842",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 582792, 582815, 582833, 582841. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76074-474208", "context_12_76074_474208", "Context at depth 12, code 76074, node 474208",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76074 and original node 474208, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-304350-582899", "context_13_304350_582899", "Context at depth 13, code 304350, node 582899",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 304350 and original node 582899, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
