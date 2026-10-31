using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0073Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0073.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0073",
        H("Original frontier context coverage 0073"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03507", "selected_cut_03507", "Selected cut at depth 14, code 111717, node 109858",
                "At remaining fuel 7 and original index 109858, selection on the full partial prefix of depth 14 and code 111717 returns the complete row with depth 14, base-four code 111717, original node 109858, kind 2, reserved field 0, 865 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03554", "selected_cut_03554", "Selected cut at depth 13, code 27980, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 27980 returns the complete row with depth 13, base-four code 27980, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-27929-109911", "unmarked_context_13_27929_109911", "Unmarked parent at depth 13, code 27929",
                "The frontier Boolean is false at remaining fuel 8, original node 109911, the whole prefixCache at depth 13 and code 27929, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-6994-111109", "unmarked_context_12_6994_111109", "Unmarked parent at depth 12, code 6994",
                "The frontier Boolean is false at remaining fuel 9, original node 111109, the whole prefixCache at depth 12 and code 6994, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-27929-109911", "node_context_13_27929_109911", "Original split at fuel 8 and node 109911",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 109842, 109858, 109890, 109910. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-6994-111109", "node_context_12_6994_111109", "Original split at fuel 9 and node 111109",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 111066, 111102, 111108. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-111717-109858", "context_14_111717_109858", "Context at depth 14, code 111717, node 109858",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 111717 and original node 109858, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-27980-3444", "context_13_27980_3444", "Context at depth 13, code 27980, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 27980 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
