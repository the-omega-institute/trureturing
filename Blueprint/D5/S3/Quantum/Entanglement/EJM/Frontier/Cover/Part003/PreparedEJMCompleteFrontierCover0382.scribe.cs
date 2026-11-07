using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0382Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0382.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0382",
        H("Original frontier context coverage 0382"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18339", "selected_cut_18339", "Selected cut at depth 12, code 71319, node 469648",
                "At remaining fuel 9 and original index 469648, selection on the full partial prefix of depth 12 and code 71319 returns the complete row with depth 12, base-four code 71319, original node 469648, kind 2, reserved field 0, 2653 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18386", "selected_cut_18386", "Selected cut at depth 10, code 4463, node 470520",
                "At remaining fuel 11 and original index 470520, selection on the full partial prefix of depth 10 and code 4463 returns the complete row with depth 10, base-four code 4463, original node 470520, kind 2, reserved field 0, 1557 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-17829-469649", "unmarked_context_11_17829_469649", "Unmarked parent at depth 11, code 17829",
                "The frontier Boolean is false at remaining fuel 10, original node 469649, the whole prefixCache at depth 11 and code 17829, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4462-470494", "unmarked_context_10_4462_470494", "Unmarked parent at depth 10, code 4462",
                "The frontier Boolean is false at remaining fuel 11, original node 470494, the whole prefixCache at depth 10 and code 4462, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-17829-469649", "node_context_11_17829_469649", "Original split at fuel 10 and node 469649",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 469595, 449506, 469617, 469648. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4462-470494", "node_context_10_4462_470494", "Original split at fuel 11 and node 470494",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 470452, 470469, 470479, 470493. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-71319-469648", "context_12_71319_469648", "Context at depth 12, code 71319, node 469648",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71319 and original node 469648, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-4463-470520", "context_10_4463_470520", "Context at depth 10, code 4463, node 470520",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4463 and original node 470520, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
