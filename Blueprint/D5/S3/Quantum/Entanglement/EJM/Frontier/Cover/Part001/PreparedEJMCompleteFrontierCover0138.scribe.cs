using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0138Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0138.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0138",
        H("Original frontier context coverage 0138"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06626", "selected_cut_06626", "Selected cut at depth 13, code 87173, node 197493",
                "At remaining fuel 8 and original index 197493, selection on the full partial prefix of depth 13 and code 87173 returns the complete row with depth 13, base-four code 87173, original node 197493, kind 2, reserved field 0, 1329 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06674", "selected_cut_06674", "Selected cut at depth 13, code 87224, node 198417",
                "At remaining fuel 8 and original index 198417, selection on the full partial prefix of depth 13 and code 87224 returns the complete row with depth 13, base-four code 87224, original node 198417, kind 2, reserved field 0, 305 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-21793-197520", "unmarked_context_12_21793_197520", "Unmarked parent at depth 12, code 21793",
                "The frontier Boolean is false at remaining fuel 9, original node 197520, the whole prefixCache at depth 12 and code 21793, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21804-198345", "unmarked_context_12_21804_198345", "Unmarked parent at depth 12, code 21804",
                "The frontier Boolean is false at remaining fuel 9, original node 198345, the whole prefixCache at depth 12 and code 21804, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-21793-197520", "node_context_12_21793_197520", "Original split at fuel 9 and node 197520",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 197474, 197493, 197512, 197519. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21804-198345", "node_context_12_21804_198345", "Original split at fuel 9 and node 198345",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 198292, 198316, 198335, 198344. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-87173-197493", "context_13_87173_197493", "Context at depth 13, code 87173, node 197493",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 87173 and original node 197493, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-87224-198417", "context_13_87224_198417", "Context at depth 13, code 87224, node 198417",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 87224 and original node 198417, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
