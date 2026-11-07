using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0177Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0177.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0177",
        H("Original frontier context coverage 0177"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08499", "selected_cut_08499", "Selected cut at depth 14, code 368808, node 238076",
                "At remaining fuel 7 and original index 238076, selection on the full partial prefix of depth 14 and code 368808 returns the complete row with depth 14, base-four code 368808, original node 238076, kind 2, reserved field 0, 1009 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08545", "selected_cut_08545", "Selected cut at depth 13, code 92224, node 239383",
                "At remaining fuel 8 and original index 239383, selection on the full partial prefix of depth 13 and code 92224 returns the complete row with depth 13, base-four code 92224, original node 239383, kind 2, reserved field 0, 2113 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-92202-238179", "unmarked_context_13_92202_238179", "Unmarked parent at depth 13, code 92202",
                "The frontier Boolean is false at remaining fuel 8, original node 238179, the whole prefixCache at depth 13 and code 92202, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1440-239355", "unmarked_context_10_1440_239355", "Unmarked parent at depth 10, code 1440",
                "The frontier Boolean is false at remaining fuel 11, original node 239355, the whole prefixCache at depth 10 and code 1440, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-92202-238179", "node_context_13_92202_238179", "Original split at fuel 8 and node 238179",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 238076, 238126, 238145, 238178. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1440-239355", "node_context_10_1440_239355", "Original split at fuel 11 and node 239355",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 236289, 237371, 238488, 239354. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-368808-238076", "context_14_368808_238076", "Context at depth 14, code 368808, node 238076",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 368808 and original node 238076, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-92224-239383", "context_13_92224_239383", "Context at depth 13, code 92224, node 239383",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92224 and original node 239383, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
