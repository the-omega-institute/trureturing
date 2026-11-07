using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0410Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0410.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0410",
        H("Original frontier context coverage 0410"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19683", "selected_cut_19683", "Selected cut at depth 13, code 289137, node 503243",
                "At remaining fuel 8 and original index 503243, selection on the full partial prefix of depth 13 and code 289137 returns the complete row with depth 13, base-four code 289137, original node 503243, kind 2, reserved field 0, 1817 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19731", "selected_cut_19731", "Selected cut at depth 13, code 289212, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 289212 returns the complete row with depth 13, base-four code 289212, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72284-503280", "unmarked_context_12_72284_503280", "Unmarked parent at depth 12, code 72284",
                "The frontier Boolean is false at remaining fuel 9, original node 503280, the whole prefixCache at depth 12 and code 72284, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72300-504226", "unmarked_context_12_72300_504226", "Unmarked parent at depth 12, code 72300",
                "The frontier Boolean is false at remaining fuel 9, original node 504226, the whole prefixCache at depth 12 and code 72300, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72284-503280", "node_context_12_72284_503280", "Original split at fuel 9 and node 503280",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 503243, 503264, 503279. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72300-504226", "node_context_12_72300_504226", "Original split at fuel 9 and node 504226",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 504170, 504209, 504225. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-289137-503243", "context_13_289137_503243", "Context at depth 13, code 289137, node 503243",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 289137 and original node 503243, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-289212-3444", "context_13_289212_3444", "Context at depth 13, code 289212, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 289212 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
