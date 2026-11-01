using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0110Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0110.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0110",
        H("Original frontier context coverage 0110"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05283", "selected_cut_05283", "Selected cut at depth 13, code 77001, node 163619",
                "At remaining fuel 8 and original index 163619, selection on the full partial prefix of depth 13 and code 77001 returns the complete row with depth 13, base-four code 77001, original node 163619, kind 2, reserved field 0, 2173 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05330", "selected_cut_05330", "Selected cut at depth 13, code 77144, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 77144 returns the complete row with depth 13, base-four code 77144, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-19250-163644", "unmarked_context_12_19250_163644", "Unmarked parent at depth 12, code 19250",
                "The frontier Boolean is false at remaining fuel 9, original node 163644, the whole prefixCache at depth 12 and code 19250, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4820-164941", "unmarked_context_11_4820_164941", "Unmarked parent at depth 11, code 4820",
                "The frontier Boolean is false at remaining fuel 10, original node 164941, the whole prefixCache at depth 11 and code 4820, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-19250-163644", "node_context_12_19250_163644", "Original split at fuel 9 and node 163644",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 163567, 163619, 163637, 163643. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4820-164941", "node_context_11_4820_164941", "Original split at fuel 10 and node 164941",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 164593, 164744, 164858, 164940. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-77001-163619", "context_13_77001_163619", "Context at depth 13, code 77001, node 163619",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 77001 and original node 163619, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-77144-3444", "context_13_77144_3444", "Context at depth 13, code 77144, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 77144 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
