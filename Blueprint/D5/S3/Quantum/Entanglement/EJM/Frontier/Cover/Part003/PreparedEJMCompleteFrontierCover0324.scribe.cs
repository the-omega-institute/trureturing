using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0324Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0324.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0324",
        H("Original frontier context coverage 0324"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15555", "selected_cut_15555", "Selected cut at depth 12, code 27801, node 398432",
                "At remaining fuel 9 and original index 398432, selection on the full partial prefix of depth 12 and code 27801 returns the complete row with depth 12, base-four code 27801, original node 398432, kind 2, reserved field 0, 2473 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15602", "selected_cut_15602", "Selected cut at depth 11, code 6971, node 399343",
                "At remaining fuel 10 and original index 399343, selection on the full partial prefix of depth 11 and code 6971 returns the complete row with depth 11, base-four code 6971, original node 399343, kind 2, reserved field 0, 809 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6950-398492", "unmarked_context_11_6950_398492", "Unmarked parent at depth 11, code 6950",
                "The frontier Boolean is false at remaining fuel 10, original node 398492, the whole prefixCache at depth 11 and code 6950, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1742-399344", "unmarked_context_10_1742_399344", "Unmarked parent at depth 10, code 1742",
                "The frontier Boolean is false at remaining fuel 11, original node 399344, the whole prefixCache at depth 10 and code 1742, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6950-398492", "node_context_11_6950_398492", "Original split at fuel 10 and node 398492",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 398405, 398432, 398456, 398491. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1742-399344", "node_context_10_1742_399344", "Original split at fuel 11 and node 399344",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 399302, 399317, 399333, 399343. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-27801-398432", "context_12_27801_398432", "Context at depth 12, code 27801, node 398432",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27801 and original node 398432, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-1742-399344", "context_10_1742_399344", "Context at depth 10, code 1742, node 399344",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1742 and original node 399344, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6968_399302, context_11_6969_399317, context_11_6970_399333, context_11_6971_399343.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
