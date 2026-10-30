using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0814Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0814.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0814",
        H("Original frontier context coverage 0814"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39076", "selected_cut_39076", "Selected cut at depth 10, code 18910, node 1058875",
                "At remaining fuel 11 and original index 1058875, selection on the full partial prefix of depth 10 and code 18910 returns the complete row with depth 10, base-four code 18910, original node 1058875, kind 2, reserved field 0, 2657 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39123", "selected_cut_39123", "Selected cut at depth 13, code 1210425, node 1059888",
                "At remaining fuel 8 and original index 1059888, selection on the full partial prefix of depth 13 and code 1210425 returns the complete row with depth 13, base-four code 1210425, original node 1059888, kind 2, reserved field 0, 1293 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-18909-1058820", "unmarked_context_10_18909_1058820", "Unmarked parent at depth 10, code 18909",
                "The frontier Boolean is false at remaining fuel 11, original node 1058820, the whole prefixCache at depth 10 and code 18909, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-302605-1059845", "unmarked_context_12_302605_1059845", "Unmarked parent at depth 12, code 302605",
                "The frontier Boolean is false at remaining fuel 9, original node 1059845, the whole prefixCache at depth 12 and code 302605, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-18909-1058820", "node_context_10_18909_1058820", "Original split at fuel 11 and node 1058820",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1058762, 1058781, 1058802, 1058819. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-302605-1059845", "node_context_12_302605_1059845", "Original split at fuel 9 and node 1059845",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1059791, 1059808, 1059833, 1059844. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-18909-1058820", "context_10_18909_1058820", "Context at depth 10, code 18909, node 1058820",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18909 and original node 1058820, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_75636_1058762, context_11_75637_1058781, context_11_75638_1058802, context_11_75639_1058819.", DescribeRole.Theorem),
            Node("context-13-1210425-1059888", "context_13_1210425_1059888", "Context at depth 13, code 1210425, node 1059888",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1210425 and original node 1059888, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
