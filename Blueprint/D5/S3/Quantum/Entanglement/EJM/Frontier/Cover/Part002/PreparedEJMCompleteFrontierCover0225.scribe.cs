using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0225Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0225.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0225",
        H("Original frontier context coverage 0225"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10802", "selected_cut_10802", "Selected cut at depth 12, code 25280, node 291245",
                "At remaining fuel 9 and original index 291245, selection on the full partial prefix of depth 12 and code 25280 returns the complete row with depth 12, base-four code 25280, original node 291245, kind 2, reserved field 0, 941 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10850", "selected_cut_10850", "Selected cut at depth 13, code 101432, node 292837",
                "At remaining fuel 8 and original index 292837, selection on the full partial prefix of depth 13 and code 101432 returns the complete row with depth 13, base-four code 101432, original node 292837, kind 2, reserved field 0, 3073 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6320-291269", "unmarked_context_11_6320_291269", "Unmarked parent at depth 11, code 6320",
                "The frontier Boolean is false at remaining fuel 10, original node 291269, the whole prefixCache at depth 11 and code 6320, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25357-292793", "unmarked_context_12_25357_292793", "Unmarked parent at depth 12, code 25357",
                "The frontier Boolean is false at remaining fuel 9, original node 292793, the whole prefixCache at depth 12 and code 25357, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6320-291269", "node_context_11_6320_291269", "Original split at fuel 10 and node 291269",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 291245, 291253, 291260, 291268. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25357-292793", "node_context_12_25357_292793", "Original split at fuel 9 and node 292793",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 292695, 292748, 292779, 292792. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25280-291245", "context_12_25280_291245", "Context at depth 12, code 25280, node 291245",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25280 and original node 291245, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-101432-292837", "context_13_101432_292837", "Context at depth 13, code 101432, node 292837",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 101432 and original node 292837, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
