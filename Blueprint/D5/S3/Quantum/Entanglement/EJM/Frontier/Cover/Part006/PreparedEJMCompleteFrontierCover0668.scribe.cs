using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0668Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0668.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0668",
        H("Original frontier context coverage 0668"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32068", "selected_cut_32068", "Selected cut at depth 13, code 431275, node 823851",
                "At remaining fuel 8 and original index 823851, selection on the full partial prefix of depth 13 and code 431275 returns the complete row with depth 13, base-four code 431275, original node 823851, kind 2, reserved field 0, 925 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32115", "selected_cut_32115", "Selected cut at depth 13, code 431325, node 824880",
                "At remaining fuel 8 and original index 824880, selection on the full partial prefix of depth 13 and code 431325 returns the complete row with depth 13, base-four code 431325, original node 824880, kind 2, reserved field 0, 3009 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-107818-823852", "unmarked_context_12_107818_823852", "Unmarked parent at depth 12, code 107818",
                "The frontier Boolean is false at remaining fuel 9, original node 823852, the whole prefixCache at depth 12 and code 107818, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-107830-824803", "unmarked_context_12_107830_824803", "Unmarked parent at depth 12, code 107830",
                "The frontier Boolean is false at remaining fuel 9, original node 824803, the whole prefixCache at depth 12 and code 107830, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-107818-823852", "node_context_12_107818_823852", "Original split at fuel 9 and node 823852",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 823799, 823819, 823840, 823851. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-107830-824803", "node_context_12_107830_824803", "Original split at fuel 9 and node 824803",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 824754, 824778, 824796, 824802. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-431275-823851", "context_13_431275_823851", "Context at depth 13, code 431275, node 823851",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 431275 and original node 823851, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-431325-824880", "context_13_431325_824880", "Context at depth 13, code 431325, node 824880",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 431325 and original node 824880, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
