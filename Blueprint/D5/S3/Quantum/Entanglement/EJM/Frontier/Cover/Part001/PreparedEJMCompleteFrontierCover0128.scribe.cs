using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0128Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0128.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0128",
        H("Original frontier context coverage 0128"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06147", "selected_cut_06147", "Selected cut at depth 13, code 84327, node 185398",
                "At remaining fuel 8 and original index 185398, selection on the full partial prefix of depth 13 and code 84327 returns the complete row with depth 13, base-four code 84327, original node 185398, kind 2, reserved field 0, 1145 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06194", "selected_cut_06194", "Selected cut at depth 13, code 84407, node 186403",
                "At remaining fuel 8 and original index 186403, selection on the full partial prefix of depth 13 and code 84407 returns the complete row with depth 13, base-four code 84407, original node 186403, kind 2, reserved field 0, 1185 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-21081-185399", "unmarked_context_12_21081_185399", "Unmarked parent at depth 12, code 21081",
                "The frontier Boolean is false at remaining fuel 9, original node 185399, the whole prefixCache at depth 12 and code 21081, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21101-186404", "unmarked_context_12_21101_186404", "Unmarked parent at depth 12, code 21101",
                "The frontier Boolean is false at remaining fuel 9, original node 186404, the whole prefixCache at depth 12 and code 21101, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-21081-185399", "node_context_12_21081_185399", "Original split at fuel 9 and node 185399",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 185358, 185386, 185398. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21101-186404", "node_context_12_21101_186404", "Original split at fuel 9 and node 186404",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 186354, 186387, 186403. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-84327-185398", "context_13_84327_185398", "Context at depth 13, code 84327, node 185398",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 84327 and original node 185398, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-21101-186404", "context_12_21101_186404", "Context at depth 12, code 21101, node 186404",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21101 and original node 186404, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_84404_3444, context_13_84405_186354, context_13_84406_186387, context_13_84407_186403.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
