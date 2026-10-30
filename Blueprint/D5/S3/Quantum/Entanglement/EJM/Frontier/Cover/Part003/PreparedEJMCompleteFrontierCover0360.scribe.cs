using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0360Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0360.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0360",
        H("Original frontier context coverage 0360"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17282", "selected_cut_17282", "Selected cut at depth 13, code 279686, node 439709",
                "At remaining fuel 8 and original index 439709, selection on the full partial prefix of depth 13 and code 279686 returns the complete row with depth 13, base-four code 279686, original node 439709, kind 2, reserved field 0, 1825 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17330", "selected_cut_17330", "Selected cut at depth 13, code 279734, node 440864",
                "At remaining fuel 8 and original index 440864, selection on the full partial prefix of depth 13 and code 279734 returns the complete row with depth 13, base-four code 279734, original node 440864, kind 2, reserved field 0, 2061 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-69921-439721", "unmarked_context_12_69921_439721", "Unmarked parent at depth 12, code 69921",
                "The frontier Boolean is false at remaining fuel 9, original node 439721, the whole prefixCache at depth 12 and code 69921, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-69932-440802", "unmarked_context_12_69932_440802", "Unmarked parent at depth 12, code 69932",
                "The frontier Boolean is false at remaining fuel 9, original node 440802, the whole prefixCache at depth 12 and code 69932, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-69921-439721", "node_context_12_69921_439721", "Original split at fuel 9 and node 439721",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 439665, 439685, 439709, 439720. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-69932-440802", "node_context_12_69932_440802", "Original split at fuel 9 and node 440802",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 440709, 440753, 440792, 440801. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-279686-439709", "context_13_279686_439709", "Context at depth 13, code 279686, node 439709",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 279686 and original node 439709, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-279734-440864", "context_13_279734_440864", "Context at depth 13, code 279734, node 440864",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 279734 and original node 440864, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
