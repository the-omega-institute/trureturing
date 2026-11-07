using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0331Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0331.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0331",
        H("Original frontier context coverage 0331"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15891", "selected_cut_15891", "Selected cut at depth 13, code 111900, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 111900 returns the complete row with depth 13, base-four code 111900, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15939", "selected_cut_15939", "Selected cut at depth 13, code 111951, node 406757",
                "At remaining fuel 8 and original index 406757, selection on the full partial prefix of depth 13 and code 111951 returns the complete row with depth 13, base-four code 111951, original node 406757, kind 2, reserved field 0, 1081 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27975-406044", "unmarked_context_12_27975_406044", "Unmarked parent at depth 12, code 27975",
                "The frontier Boolean is false at remaining fuel 9, original node 406044, the whole prefixCache at depth 12 and code 27975, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27986-406680", "unmarked_context_12_27986_406680", "Unmarked parent at depth 12, code 27986",
                "The frontier Boolean is false at remaining fuel 9, original node 406680, the whole prefixCache at depth 12 and code 27986, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27975-406044", "node_context_12_27975_406044", "Original split at fuel 9 and node 406044",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 406012, 406035, 406043. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27986-406680", "node_context_12_27986_406680", "Original split at fuel 9 and node 406680",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 406641, 406672, 406679. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-111900-3444", "context_13_111900_3444", "Context at depth 13, code 111900, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111900 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-111951-406757", "context_13_111951_406757", "Context at depth 13, code 111951, node 406757",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111951 and original node 406757, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
