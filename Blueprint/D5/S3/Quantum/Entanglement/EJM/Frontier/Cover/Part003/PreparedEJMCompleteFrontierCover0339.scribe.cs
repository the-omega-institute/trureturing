using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0339Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0339.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0339",
        H("Original frontier context coverage 0339"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16276", "selected_cut_16276", "Selected cut at depth 13, code 112795, node 414693",
                "At remaining fuel 8 and original index 414693, selection on the full partial prefix of depth 13 and code 112795 returns the complete row with depth 13, base-four code 112795, original node 414693, kind 2, reserved field 0, 833 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16323", "selected_cut_16323", "Selected cut at depth 13, code 112845, node 415713",
                "At remaining fuel 8 and original index 415713, selection on the full partial prefix of depth 13 and code 112845 returns the complete row with depth 13, base-four code 112845, original node 415713, kind 2, reserved field 0, 2761 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28198-414694", "unmarked_context_12_28198_414694", "Unmarked parent at depth 12, code 28198",
                "The frontier Boolean is false at remaining fuel 9, original node 414694, the whole prefixCache at depth 12 and code 28198, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-28210-415653", "unmarked_context_12_28210_415653", "Unmarked parent at depth 12, code 28210",
                "The frontier Boolean is false at remaining fuel 9, original node 415653, the whole prefixCache at depth 12 and code 28210, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28198-414694", "node_context_12_28198_414694", "Original split at fuel 9 and node 414694",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 414645, 414669, 414683, 414693. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-28210-415653", "node_context_12_28210_415653", "Original split at fuel 9 and node 415653",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 415607, 415632, 415647, 415652. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-112795-414693", "context_13_112795_414693", "Context at depth 13, code 112795, node 414693",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112795 and original node 414693, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-112845-415713", "context_13_112845_415713", "Context at depth 13, code 112845, node 415713",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112845 and original node 415713, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
