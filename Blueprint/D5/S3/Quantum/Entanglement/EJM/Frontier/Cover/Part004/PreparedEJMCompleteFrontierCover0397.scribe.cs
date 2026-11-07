using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0397Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0397.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0397",
        H("Original frontier context coverage 0397"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19058", "selected_cut_19058", "Selected cut at depth 13, code 288008, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 288008 returns the complete row with depth 13, base-four code 288008, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19106", "selected_cut_19106", "Selected cut at depth 13, code 288059, node 489344",
                "At remaining fuel 8 and original index 489344, selection on the full partial prefix of depth 13 and code 288059 returns the complete row with depth 13, base-four code 288059, original node 489344, kind 2, reserved field 0, 1209 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72002-488633", "unmarked_context_12_72002_488633", "Unmarked parent at depth 12, code 72002",
                "The frontier Boolean is false at remaining fuel 9, original node 488633, the whole prefixCache at depth 12 and code 72002, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72014-489345", "unmarked_context_12_72014_489345", "Unmarked parent at depth 12, code 72014",
                "The frontier Boolean is false at remaining fuel 9, original node 489345, the whole prefixCache at depth 12 and code 72014, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72002-488633", "node_context_12_72002_488633", "Original split at fuel 9 and node 488633",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 488571, 488620, 488632. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72014-489345", "node_context_12_72014_489345", "Original split at fuel 9 and node 489345",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 489299, 489333, 489344. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-288008-3444", "context_13_288008_3444", "Context at depth 13, code 288008, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288008 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-72014-489345", "context_12_72014_489345", "Context at depth 12, code 72014, node 489345",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72014 and original node 489345, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_288056_3444, context_13_288057_489299, context_13_288058_489333, context_13_288059_489344.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
