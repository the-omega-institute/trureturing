using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1065Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1065.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1065",
        H("Original frontier context coverage 1065"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51122", "selected_cut_51122", "Selected cut at depth 10, code 69656, node 1469906",
                "At remaining fuel 11 and original index 1469906, selection on the full partial prefix of depth 10 and code 69656 returns the complete row with depth 10, base-four code 69656, original node 1469906, kind 2, reserved field 0, 2973 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51169", "selected_cut_51169", "Selected cut at depth 10, code 69715, node 3440",
                "At remaining fuel 11 and original index 3440, selection on the full partial prefix of depth 10 and code 69715 returns the complete row with depth 10, base-four code 69715, original node 3440, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-17413-1469809", "unmarked_context_9_17413_1469809", "Unmarked parent at depth 9, code 17413",
                "The frontier Boolean is false at remaining fuel 12, original node 1469809, the whole prefixCache at depth 9 and code 17413, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-69714-1471850", "unmarked_context_10_69714_1471850", "Unmarked parent at depth 10, code 69714",
                "The frontier Boolean is false at remaining fuel 11, original node 1471850, the whole prefixCache at depth 10 and code 69714, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-17413-1469809", "node_context_9_17413_1469809", "Original split at fuel 12 and node 1469809",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1469663, 1468874, 1469808, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-69714-1471850", "node_context_10_69714_1471850", "Original split at fuel 11 and node 1471850",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1471735, 1471794, 1468743, 1471849. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-17413-1469809", "context_9_17413_1469809", "Context at depth 9, code 17413, node 1469809",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 17413 and original node 1469809, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_69652_1469663, context_10_69653_1468874, context_10_69654_1469808, context_10_69655_3440.", DescribeRole.Theorem),
            Node("context-10-69715-3440", "context_10_69715_3440", "Context at depth 10, code 69715, node 3440",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 69715 and original node 3440, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
