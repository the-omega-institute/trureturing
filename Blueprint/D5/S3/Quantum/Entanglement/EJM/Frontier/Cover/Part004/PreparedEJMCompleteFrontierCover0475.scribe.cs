using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0475Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0475.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0475",
        H("Original frontier context coverage 0475"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22803", "selected_cut_22803", "Selected cut at depth 12, code 75933, node 579527",
                "At remaining fuel 9 and original index 579527, selection on the full partial prefix of depth 12 and code 75933 returns the complete row with depth 12, base-four code 75933, original node 579527, kind 2, reserved field 0, 2205 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22849", "selected_cut_22849", "Selected cut at depth 13, code 304159, node 580431",
                "At remaining fuel 8 and original index 580431, selection on the full partial prefix of depth 13 and code 304159 returns the complete row with depth 13, base-four code 304159, original node 580431, kind 2, reserved field 0, 1013 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18983-579580", "unmarked_context_11_18983_579580", "Unmarked parent at depth 11, code 18983",
                "The frontier Boolean is false at remaining fuel 10, original node 579580, the whole prefixCache at depth 11 and code 18983, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19009-580433", "unmarked_context_11_19009_580433", "Unmarked parent at depth 11, code 19009",
                "The frontier Boolean is false at remaining fuel 10, original node 580433, the whole prefixCache at depth 11 and code 19009, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18983-579580", "node_context_11_18983_579580", "Original split at fuel 10 and node 579580",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 579487, 579527, 579560, 579579. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19009-580433", "node_context_11_19009_580433", "Original split at fuel 10 and node 580433",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 34034, 88909, 580432. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75933-579527", "context_12_75933_579527", "Context at depth 12, code 75933, node 579527",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75933 and original node 579527, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-19009-580433", "context_11_19009_580433", "Context at depth 11, code 19009, node 580433",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19009 and original node 580433, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_76036_448748, context_12_76037_34034, context_12_76038_88909, context_12_76039_580432.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
