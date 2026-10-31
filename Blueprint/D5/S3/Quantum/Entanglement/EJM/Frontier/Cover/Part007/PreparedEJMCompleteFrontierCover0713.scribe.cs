using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0713Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0713.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0713",
        H("Original frontier context coverage 0713"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34228", "selected_cut_34228", "Selected cut at depth 11, code 28267, node 884273",
                "At remaining fuel 10 and original index 884273, selection on the full partial prefix of depth 11 and code 28267 returns the complete row with depth 11, base-four code 28267, original node 884273, kind 2, reserved field 0, 3485 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34275", "selected_cut_34275", "Selected cut at depth 13, code 452694, node 885987",
                "At remaining fuel 8 and original index 885987, selection on the full partial prefix of depth 13 and code 452694 returns the complete row with depth 13, base-four code 452694, original node 885987, kind 2, reserved field 0, 1341 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-7066-884274", "unmarked_context_10_7066_884274", "Unmarked parent at depth 10, code 7066",
                "The frontier Boolean is false at remaining fuel 11, original node 884274, the whole prefixCache at depth 10 and code 7066, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-113172-885886", "unmarked_context_12_113172_885886", "Unmarked parent at depth 12, code 113172",
                "The frontier Boolean is false at remaining fuel 9, original node 885886, the whole prefixCache at depth 12 and code 113172, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-7066-884274", "node_context_10_7066_884274", "Original split at fuel 11 and node 884274",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 884203, 884228, 479708, 884273. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-113172-885886", "node_context_12_113172_885886", "Original split at fuel 9 and node 885886",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 885820, 885853, 885873, 885885. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-28267-884273", "context_11_28267_884273", "Context at depth 11, code 28267, node 884273",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 28267 and original node 884273, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-452694-885987", "context_13_452694_885987", "Context at depth 13, code 452694, node 885987",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 452694 and original node 885987, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
