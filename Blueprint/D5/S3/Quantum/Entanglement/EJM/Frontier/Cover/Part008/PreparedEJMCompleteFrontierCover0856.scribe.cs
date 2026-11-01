using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0856Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0856.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0856",
        H("Original frontier context coverage 0856"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41090", "selected_cut_41090", "Selected cut at depth 12, code 333956, node 1121797",
                "At remaining fuel 9 and original index 1121797, selection on the full partial prefix of depth 12 and code 333956 returns the complete row with depth 12, base-four code 333956, original node 1121797, kind 2, reserved field 0, 1201 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41138", "selected_cut_41138", "Selected cut at depth 12, code 334355, node 1123709",
                "At remaining fuel 9 and original index 1123709, selection on the full partial prefix of depth 12 and code 334355 returns the complete row with depth 12, base-four code 334355, original node 1123709, kind 2, reserved field 0, 4037 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83489-1121872", "unmarked_context_11_83489_1121872", "Unmarked parent at depth 11, code 83489",
                "The frontier Boolean is false at remaining fuel 10, original node 1121872, the whole prefixCache at depth 11 and code 83489, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-20896-1123455", "unmarked_context_10_20896_1123455", "Unmarked parent at depth 10, code 20896",
                "The frontier Boolean is false at remaining fuel 11, original node 1123455, the whole prefixCache at depth 10 and code 20896, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83489-1121872", "node_context_11_83489_1121872", "Original split at fuel 10 and node 1121872",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1121797, 1121832, 1121852, 1121871. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-20896-1123455", "node_context_10_20896_1123455", "Original split at fuel 11 and node 1123455",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 1123069, 1123221, 1123454. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-333956-1121797", "context_12_333956_1121797", "Context at depth 12, code 333956, node 1121797",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 333956 and original node 1121797, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-334355-1123709", "context_12_334355_1123709", "Context at depth 12, code 334355, node 1123709",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 334355 and original node 1123709, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
