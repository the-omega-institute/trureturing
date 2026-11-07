using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0334Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0334.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0334",
        H("Original frontier context coverage 0334"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16035", "selected_cut_16035", "Selected cut at depth 12, code 28020, node 408409",
                "At remaining fuel 9 and original index 408409, selection on the full partial prefix of depth 12 and code 28020 returns the complete row with depth 12, base-four code 28020, original node 408409, kind 2, reserved field 0, 3025 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16083", "selected_cut_16083", "Selected cut at depth 12, code 28062, node 409831",
                "At remaining fuel 9 and original index 409831, selection on the full partial prefix of depth 12 and code 28062 returns the complete row with depth 12, base-four code 28062, original node 409831, kind 2, reserved field 0, 1981 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-7005-408479", "unmarked_context_11_7005_408479", "Unmarked parent at depth 11, code 7005",
                "The frontier Boolean is false at remaining fuel 10, original node 408479, the whole prefixCache at depth 11 and code 7005, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-7014-409766", "unmarked_context_11_7014_409766", "Unmarked parent at depth 11, code 7014",
                "The frontier Boolean is false at remaining fuel 10, original node 409766, the whole prefixCache at depth 11 and code 7014, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-7005-408479", "node_context_11_7005_408479", "Original split at fuel 10 and node 408479",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 408409, 126884, 408441, 408478. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-7014-409766", "node_context_11_7014_409766", "Original split at fuel 10 and node 409766",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 409693, 409714, 409741, 409765. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-28020-408409", "context_12_28020_408409", "Context at depth 12, code 28020, node 408409",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28020 and original node 408409, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-28062-409831", "context_12_28062_409831", "Context at depth 12, code 28062, node 409831",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28062 and original node 409831, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
