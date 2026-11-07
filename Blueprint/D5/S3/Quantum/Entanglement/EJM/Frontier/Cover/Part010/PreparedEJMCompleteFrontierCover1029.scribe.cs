using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1029Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1029.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1029",
        H("Original frontier context coverage 1029"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49395", "selected_cut_49395", "Selected cut at depth 12, code 407364, node 1397223",
                "At remaining fuel 9 and original index 1397223, selection on the full partial prefix of depth 12 and code 407364 returns the complete row with depth 12, base-four code 407364, original node 1397223, kind 2, reserved field 0, 1357 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49442", "selected_cut_49442", "Selected cut at depth 12, code 407585, node 1398733",
                "At remaining fuel 9 and original index 1398733, selection on the full partial prefix of depth 12 and code 407585 returns the complete row with depth 12, base-four code 407585, original node 1398733, kind 2, reserved field 0, 1761 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-101841-1397265", "unmarked_context_11_101841_1397265", "Unmarked parent at depth 11, code 101841",
                "The frontier Boolean is false at remaining fuel 10, original node 1397265, the whole prefixCache at depth 11 and code 101841, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25473-1398694", "unmarked_context_10_25473_1398694", "Unmarked parent at depth 10, code 25473",
                "The frontier Boolean is false at remaining fuel 11, original node 1398694, the whole prefixCache at depth 10 and code 25473, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-101841-1397265", "node_context_11_101841_1397265", "Original split at fuel 10 and node 1397265",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1397223, 642341, 1397241, 1397264. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25473-1398694", "node_context_10_25473_1398694", "Original split at fuel 11 and node 1398694",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1398447, 1398494, 1398594, 1398693. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-407364-1397223", "context_12_407364_1397223", "Context at depth 12, code 407364, node 1397223",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 407364 and original node 1397223, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-407585-1398733", "context_12_407585_1398733", "Context at depth 12, code 407585, node 1398733",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 407585 and original node 1398733, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
