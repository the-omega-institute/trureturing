using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0504Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0504.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0504",
        H("Original frontier context coverage 0504"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24195", "selected_cut_24195", "Selected cut at depth 12, code 76965, node 612131",
                "At remaining fuel 9 and original index 612131, selection on the full partial prefix of depth 12 and code 76965 returns the complete row with depth 12, base-four code 76965, original node 612131, kind 2, reserved field 0, 1813 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24242", "selected_cut_24242", "Selected cut at depth 12, code 77066, node 524302",
                "At remaining fuel 9 and original index 524302, selection on the full partial prefix of depth 12 and code 77066 returns the complete row with depth 12, base-four code 77066, original node 524302, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19241-612184", "unmarked_context_11_19241_612184", "Unmarked parent at depth 11, code 19241",
                "The frontier Boolean is false at remaining fuel 10, original node 612184, the whole prefixCache at depth 11 and code 19241, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77065-613323", "unmarked_context_12_77065_613323", "Unmarked parent at depth 12, code 77065",
                "The frontier Boolean is false at remaining fuel 9, original node 613323, the whole prefixCache at depth 12 and code 77065, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19241-612184", "node_context_11_19241_612184", "Original split at fuel 10 and node 612184",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 612109, 612131, 612147, 612183. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77065-613323", "node_context_12_77065_613323", "Original split at fuel 9 and node 613323",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 613185, 613236, 613299, 613322. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76965-612131", "context_12_76965_612131", "Context at depth 12, code 76965, node 612131",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76965 and original node 612131, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-77066-524302", "context_12_77066_524302", "Context at depth 12, code 77066, node 524302",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77066 and original node 524302, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
