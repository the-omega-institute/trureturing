using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0276Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0276.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0276",
        H("Original frontier context coverage 0276"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13251", "selected_cut_13251", "Selected cut at depth 13, code 106572, node 349591",
                "At remaining fuel 8 and original index 349591, selection on the full partial prefix of depth 13 and code 106572 returns the complete row with depth 13, base-four code 106572, original node 349591, kind 2, reserved field 0, 1513 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13298", "selected_cut_13298", "Selected cut at depth 13, code 106619, node 350400",
                "At remaining fuel 8 and original index 350400, selection on the full partial prefix of depth 13 and code 106619 returns the complete row with depth 13, base-four code 106619, original node 350400, kind 2, reserved field 0, 737 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26642-349574", "unmarked_context_12_26642_349574", "Unmarked parent at depth 12, code 26642",
                "The frontier Boolean is false at remaining fuel 9, original node 349574, the whole prefixCache at depth 12 and code 26642, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26654-350401", "unmarked_context_12_26654_350401", "Unmarked parent at depth 12, code 26654",
                "The frontier Boolean is false at remaining fuel 9, original node 350401, the whole prefixCache at depth 12 and code 26654, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26642-349574", "node_context_12_26642_349574", "Original split at fuel 9 and node 349574",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 349520, 349547, 349565, 349573. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26654-350401", "node_context_12_26654_350401", "Original split at fuel 9 and node 350401",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 350350, 350375, 350394, 350400. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26642-349574", "context_12_26642_349574", "Context at depth 12, code 26642, node 349574",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26642 and original node 349574, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_106568_349520, context_13_106569_349547, context_13_106570_349565, context_13_106571_349573.", DescribeRole.Theorem),
            Node("context-12-26654-350401", "context_12_26654_350401", "Context at depth 12, code 26654, node 350401",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26654 and original node 350401, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_106616_350350, context_13_106617_350375, context_13_106618_350394, context_13_106619_350400.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
