using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1057Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1057.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1057",
        H("Original frontier context coverage 1057"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50740", "selected_cut_50740", "Selected cut at depth 10, code 27550, node 1452749",
                "At remaining fuel 11 and original index 1452749, selection on the full partial prefix of depth 10 and code 27550 returns the complete row with depth 10, base-four code 27550, original node 1452749, kind 2, reserved field 0, 681 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50787", "selected_cut_50787", "Selected cut at depth 12, code 441105, node 1454742",
                "At remaining fuel 9 and original index 1454742, selection on the full partial prefix of depth 12 and code 441105 returns the complete row with depth 12, base-four code 441105, original node 1454742, kind 2, reserved field 0, 2185 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-6887-1452754", "unmarked_context_9_6887_1452754", "Unmarked parent at depth 9, code 6887",
                "The frontier Boolean is false at remaining fuel 12, original node 1452754, the whole prefixCache at depth 9 and code 6887, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-1722-1454555", "unmarked_context_8_1722_1454555", "Unmarked parent at depth 8, code 1722",
                "The frontier Boolean is false at remaining fuel 13, original node 1454555, the whole prefixCache at depth 8 and code 1722, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-6887-1452754", "node_context_9_6887_1452754", "Original split at fuel 12 and node 1452754",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1452669, 1452715, 1452749, 1452753. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-1722-1454555", "node_context_8_1722_1454555", "Original split at fuel 13 and node 1454555",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1453760, 1454190, 1454433, 1454554. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-27550-1452749", "context_10_27550_1452749", "Context at depth 10, code 27550, node 1452749",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 27550 and original node 1452749, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-441105-1454742", "context_12_441105_1454742", "Context at depth 12, code 441105, node 1454742",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 441105 and original node 1454742, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
