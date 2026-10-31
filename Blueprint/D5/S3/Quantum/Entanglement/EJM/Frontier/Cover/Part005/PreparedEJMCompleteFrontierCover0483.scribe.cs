using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0483Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0483.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0483",
        H("Original frontier context coverage 0483"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23188", "selected_cut_23188", "Selected cut at depth 12, code 76222, node 586744",
                "At remaining fuel 9 and original index 586744, selection on the full partial prefix of depth 12 and code 76222 returns the complete row with depth 12, base-four code 76222, original node 586744, kind 2, reserved field 0, 1189 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23234", "selected_cut_23234", "Selected cut at depth 13, code 305225, node 588042",
                "At remaining fuel 8 and original index 588042, selection on the full partial prefix of depth 13 and code 305225 returns the complete row with depth 13, base-four code 305225, original node 588042, kind 2, reserved field 0, 1809 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19055-586755", "unmarked_context_11_19055_586755", "Unmarked parent at depth 11, code 19055",
                "The frontier Boolean is false at remaining fuel 10, original node 586755, the whole prefixCache at depth 11 and code 19055, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76305-587980", "unmarked_context_12_76305_587980", "Unmarked parent at depth 12, code 76305",
                "The frontier Boolean is false at remaining fuel 9, original node 587980, the whole prefixCache at depth 12 and code 76305, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19055-586755", "node_context_11_19055_586755", "Original split at fuel 10 and node 586755",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 586721, 586731, 586744, 586754. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76305-587980", "node_context_12_76305_587980", "Original split at fuel 9 and node 587980",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 587897, 587934, 587957, 587979. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76222-586744", "context_12_76222_586744", "Context at depth 12, code 76222, node 586744",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76222 and original node 586744, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-305225-588042", "context_13_305225_588042", "Context at depth 13, code 305225, node 588042",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 305225 and original node 588042, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
