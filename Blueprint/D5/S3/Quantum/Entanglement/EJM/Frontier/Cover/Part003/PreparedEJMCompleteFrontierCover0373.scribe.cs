using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0373Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0373.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0373",
        H("Original frontier context coverage 0373"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17907", "selected_cut_17907", "Selected cut at depth 13, code 283812, node 458122",
                "At remaining fuel 8 and original index 458122, selection on the full partial prefix of depth 13 and code 283812 returns the complete row with depth 13, base-four code 283812, original node 458122, kind 2, reserved field 0, 841 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17953", "selected_cut_17953", "Selected cut at depth 11, code 17749, node 459416",
                "At remaining fuel 10 and original index 459416, selection on the full partial prefix of depth 11 and code 17749 returns the complete row with depth 11, base-four code 17749, original node 459416, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-70952-458094", "unmarked_context_12_70952_458094", "Unmarked parent at depth 12, code 70952",
                "The frontier Boolean is false at remaining fuel 9, original node 458094, the whole prefixCache at depth 12 and code 70952, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-17748-459882", "unmarked_context_11_17748_459882", "Unmarked parent at depth 11, code 17748",
                "The frontier Boolean is false at remaining fuel 10, original node 459882, the whole prefixCache at depth 11 and code 17748, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-70952-458094", "node_context_12_70952_458094", "Original split at fuel 9 and node 458094",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 457874, 457952, 458035, 458093. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-17748-459882", "node_context_11_17748_459882", "Original split at fuel 10 and node 459882",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 459814, 455939, 459881, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-70952-458094", "context_12_70952_458094", "Context at depth 12, code 70952, node 458094",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 70952 and original node 458094, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_283808_457874, context_13_283809_457952, context_13_283810_458035, context_13_283811_458093.", DescribeRole.Theorem),
            Node("context-11-17749-459416", "context_11_17749_459416", "Context at depth 11, code 17749, node 459416",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 17749 and original node 459416, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
