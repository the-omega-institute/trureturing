using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0135Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0135.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0135",
        H("Original frontier context coverage 0135"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06482", "selected_cut_06482", "Selected cut at depth 11, code 5399, node 1736",
                "At remaining fuel 10 and original index 1736, selection on the full partial prefix of depth 11 and code 5399 returns the complete row with depth 11, base-four code 5399, original node 1736, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06529", "selected_cut_06529", "Selected cut at depth 12, code 21649, node 194875",
                "At remaining fuel 9 and original index 194875, selection on the full partial prefix of depth 12 and code 21649 returns the complete row with depth 12, base-four code 21649, original node 194875, kind 2, reserved field 0, 1997 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1349-193412", "unmarked_context_10_1349_193412", "Unmarked parent at depth 10, code 1349",
                "The frontier Boolean is false at remaining fuel 11, original node 193412, the whole prefixCache at depth 10 and code 1349, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1352-194781", "unmarked_context_10_1352_194781", "Unmarked parent at depth 10, code 1352",
                "The frontier Boolean is false at remaining fuel 11, original node 194781, the whole prefixCache at depth 10 and code 1352, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1349-193412", "node_context_10_1349_193412", "Original split at fuel 11 and node 193412",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 193104, 193190, 193411, 1736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1352-194781", "node_context_10_1352_194781", "Original split at fuel 11 and node 194781",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 194401, 194551, 194673, 194780. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5399-1736", "context_11_5399_1736", "Context at depth 11, code 5399, node 1736",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5399 and original node 1736, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-21649-194875", "context_12_21649_194875", "Context at depth 12, code 21649, node 194875",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21649 and original node 194875, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
