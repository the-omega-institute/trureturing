using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0647Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0647.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0647",
        H("Original frontier context coverage 0647"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31059", "selected_cut_31059", "Selected cut at depth 13, code 422022, node 790993",
                "At remaining fuel 8 and original index 790993, selection on the full partial prefix of depth 13 and code 422022 returns the complete row with depth 13, base-four code 422022, original node 790993, kind 2, reserved field 0, 1161 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31107", "selected_cut_31107", "Selected cut at depth 13, code 422070, node 792106",
                "At remaining fuel 8 and original index 792106, selection on the full partial prefix of depth 13 and code 422070 returns the complete row with depth 13, base-four code 422070, original node 792106, kind 2, reserved field 0, 1441 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-105505-791004", "unmarked_context_12_105505_791004", "Unmarked parent at depth 12, code 105505",
                "The frontier Boolean is false at remaining fuel 9, original node 791004, the whole prefixCache at depth 12 and code 105505, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-105516-792033", "unmarked_context_12_105516_792033", "Unmarked parent at depth 12, code 105516",
                "The frontier Boolean is false at remaining fuel 9, original node 792033, the whole prefixCache at depth 12 and code 105516, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-105505-791004", "node_context_12_105505_791004", "Original split at fuel 9 and node 791004",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 790928, 790972, 790993, 791003. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-105516-792033", "node_context_12_105516_792033", "Original split at fuel 9 and node 792033",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 791979, 792005, 792025, 792032. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-422022-790993", "context_13_422022_790993", "Context at depth 13, code 422022, node 790993",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 422022 and original node 790993, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-422070-792106", "context_13_422070_792106", "Context at depth 13, code 422070, node 792106",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 422070 and original node 792106, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
