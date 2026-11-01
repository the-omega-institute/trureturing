using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0072Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0072.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0072",
        H("Original frontier context coverage 0072"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03460", "selected_cut_03460", "Selected cut at depth 13, code 27823, node 108805",
                "At remaining fuel 8 and original index 108805, selection on the full partial prefix of depth 13 and code 27823 returns the complete row with depth 13, base-four code 27823, original node 108805, kind 2, reserved field 0, 1225 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03506", "selected_cut_03506", "Selected cut at depth 14, code 111716, node 109842",
                "At remaining fuel 7 and original index 109842, selection on the full partial prefix of depth 14 and code 111716 returns the complete row with depth 14, base-four code 111716, original node 109842, kind 2, reserved field 0, 813 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-6955-108806", "unmarked_context_12_6955_108806", "Unmarked parent at depth 12, code 6955",
                "The frontier Boolean is false at remaining fuel 9, original node 108806, the whole prefixCache at depth 12 and code 6955, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-6981-109823", "unmarked_context_12_6981_109823", "Unmarked parent at depth 12, code 6981",
                "The frontier Boolean is false at remaining fuel 9, original node 109823, the whole prefixCache at depth 12 and code 6981, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-6955-108806", "node_context_12_6955_108806", "Original split at fuel 9 and node 108806",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 108656, 108745, 108792, 108805. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-6981-109823", "node_context_12_6981_109823", "Original split at fuel 9 and node 109823",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 109770, 109808, 109822. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-27823-108805", "context_13_27823_108805", "Context at depth 13, code 27823, node 108805",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 27823 and original node 108805, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-111716-109842", "context_14_111716_109842", "Context at depth 14, code 111716, node 109842",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 111716 and original node 109842, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
