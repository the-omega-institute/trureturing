using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0166Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0166.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0166",
        H("Original frontier context coverage 0166"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07971", "selected_cut_07971", "Selected cut at depth 13, code 91200, node 227446",
                "At remaining fuel 8 and original index 227446, selection on the full partial prefix of depth 13 and code 91200 returns the complete row with depth 13, base-four code 91200, original node 227446, kind 2, reserved field 0, 1773 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08018", "selected_cut_08018", "Selected cut at depth 13, code 91247, node 228433",
                "At remaining fuel 8 and original index 228433, selection on the full partial prefix of depth 13 and code 91247 returns the complete row with depth 13, base-four code 91247, original node 228433, kind 2, reserved field 0, 893 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5699-227428", "unmarked_context_11_5699_227428", "Unmarked parent at depth 11, code 5699",
                "The frontier Boolean is false at remaining fuel 10, original node 227428, the whole prefixCache at depth 11 and code 5699, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22811-228434", "unmarked_context_12_22811_228434", "Unmarked parent at depth 12, code 22811",
                "The frontier Boolean is false at remaining fuel 9, original node 228434, the whole prefixCache at depth 12 and code 22811, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5699-227428", "node_context_11_5699_227428", "Original split at fuel 10 and node 227428",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 227042, 227128, 227286, 227427. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22811-228434", "node_context_12_22811_228434", "Original split at fuel 9 and node 228434",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 228362, 228402, 228426, 228433. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5699-227428", "context_11_5699_227428", "Context at depth 11, code 5699, node 227428",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5699 and original node 227428, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_22796_227042, context_12_22797_227128, context_12_22798_227286, context_12_22799_227427.", DescribeRole.Theorem),
            Node("context-12-22811-228434", "context_12_22811_228434", "Context at depth 12, code 22811, node 228434",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22811 and original node 228434, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_91244_228362, context_13_91245_228402, context_13_91246_228426, context_13_91247_228433.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
