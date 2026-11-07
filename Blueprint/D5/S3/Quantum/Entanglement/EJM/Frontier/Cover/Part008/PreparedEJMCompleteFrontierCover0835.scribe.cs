using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0835Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0835.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0835",
        H("Original frontier context coverage 0835"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40084", "selected_cut_40084", "Selected cut at depth 12, code 308590, node 1088561",
                "At remaining fuel 9 and original index 1088561, selection on the full partial prefix of depth 12 and code 308590 returns the complete row with depth 12, base-four code 308590, original node 1088561, kind 2, reserved field 0, 1945 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40130", "selected_cut_40130", "Selected cut at depth 13, code 1234964, node 1089828",
                "At remaining fuel 8 and original index 1089828, selection on the full partial prefix of depth 13 and code 1234964 returns the complete row with depth 13, base-four code 1234964, original node 1089828, kind 2, reserved field 0, 1833 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-77147-1088595", "unmarked_context_11_77147_1088595", "Unmarked parent at depth 11, code 77147",
                "The frontier Boolean is false at remaining fuel 10, original node 1088595, the whole prefixCache at depth 11 and code 77147, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-1205-1089790", "unmarked_context_8_1205_1089790", "Unmarked parent at depth 8, code 1205",
                "The frontier Boolean is false at remaining fuel 13, original node 1089790, the whole prefixCache at depth 8 and code 1205, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-77147-1088595", "node_context_11_77147_1088595", "Original split at fuel 10 and node 1088595",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1088505, 1088529, 1088561, 1088594. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-1205-1089790", "node_context_8_1205_1089790", "Original split at fuel 13 and node 1089790",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1087634, 1088917, 1089491, 1089789. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-308590-1088561", "context_12_308590_1088561", "Context at depth 12, code 308590, node 1088561",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 308590 and original node 1088561, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1234964-1089828", "context_13_1234964_1089828", "Context at depth 13, code 1234964, node 1089828",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1234964 and original node 1089828, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
