using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0768Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0768.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0768",
        H("Original frontier context coverage 0768"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36867", "selected_cut_36867", "Selected cut at depth 12, code 297738, node 982260",
                "At remaining fuel 9 and original index 982260, selection on the full partial prefix of depth 12 and code 297738 returns the complete row with depth 12, base-four code 297738, original node 982260, kind 2, reserved field 0, 1825 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36912", "selected_cut_36912", "Selected cut at depth 7, code 291, node 984703",
                "At remaining fuel 14 and original index 984703, selection on the full partial prefix of depth 7 and code 291 returns the complete row with depth 7, base-four code 291, original node 984703, kind 2, reserved field 0, 5 subtree occurrences and completion domain 67108864. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-74434-982325", "unmarked_context_11_74434_982325", "Unmarked parent at depth 11, code 74434",
                "The frontier Boolean is false at remaining fuel 10, original node 982325, the whole prefixCache at depth 11 and code 74434, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-6-72-984704", "unmarked_context_6_72_984704", "Unmarked parent at depth 6, code 72",
                "The frontier Boolean is false at remaining fuel 15, original node 984704, the whole prefixCache at depth 6 and code 72, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-74434-982325", "node_context_11_74434_982325", "Original split at fuel 10 and node 982325",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 895, 895, 982260, 982324. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-6-72-984704", "node_context_6_72_984704", "Original split at fuel 15 and node 984704",
                "The complete original decoder output is the split at coordinate 6, with value children 0 through 3 respectively at original indices 116316, 116316, 984702, 984703. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-297738-982260", "context_12_297738_982260", "Context at depth 12, code 297738, node 982260",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 297738 and original node 982260, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-6-72-984704", "context_6_72_984704", "Context at depth 6, code 72, node 984704",
                "The conclusion is adaptive Accepted at the exact depth 6, full base-four code 72 and original node 984704, hence remaining fuel 15, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_7_288_116316, context_7_289_116316, context_7_290_984702, context_7_291_984703.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
