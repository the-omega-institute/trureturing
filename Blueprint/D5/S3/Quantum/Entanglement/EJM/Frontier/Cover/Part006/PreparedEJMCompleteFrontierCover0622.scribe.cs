using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0622Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0622.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0622",
        H("Original frontier context coverage 0622"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29860", "selected_cut_29860", "Selected cut at depth 12, code 93835, node 753717",
                "At remaining fuel 9 and original index 753717, selection on the full partial prefix of depth 12 and code 93835 returns the complete row with depth 12, base-four code 93835, original node 753717, kind 2, reserved field 0, 2221 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29906", "selected_cut_29906", "Selected cut at depth 11, code 23471, node 754701",
                "At remaining fuel 10 and original index 754701, selection on the full partial prefix of depth 11 and code 23471 returns the complete row with depth 11, base-four code 23471, original node 754701, kind 2, reserved field 0, 2413 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23458-753718", "unmarked_context_11_23458_753718", "Unmarked parent at depth 11, code 23458",
                "The frontier Boolean is false at remaining fuel 10, original node 753718, the whole prefixCache at depth 11 and code 23458, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1466-754703", "unmarked_context_9_1466_754703", "Unmarked parent at depth 9, code 1466",
                "The frontier Boolean is false at remaining fuel 12, original node 754703, the whole prefixCache at depth 9 and code 1466, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23458-753718", "node_context_11_23458_753718", "Original split at fuel 10 and node 753718",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 753663, 753689, 448662, 753717. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1466-754703", "node_context_9_1466_754703", "Original split at fuel 12 and node 754703",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 753827, 754236, 754516, 754702. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93835-753717", "context_12_93835_753717", "Context at depth 12, code 93835, node 753717",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93835 and original node 753717, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-1466-754703", "context_9_1466_754703", "Context at depth 9, code 1466, node 754703",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 1466 and original node 754703, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_5864_753827, context_10_5865_754236, context_10_5866_754516, context_10_5867_754702.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
