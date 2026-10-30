using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0752Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0752.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0752",
        H("Original frontier context coverage 0752"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36098", "selected_cut_36098", "Selected cut at depth 10, code 18005, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 18005 returns the complete row with depth 10, base-four code 18005, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36146", "selected_cut_36146", "Selected cut at depth 13, code 1153058, node 954913",
                "At remaining fuel 8 and original index 954913, selection on the full partial prefix of depth 13 and code 1153058 returns the complete row with depth 13, base-four code 1153058, original node 954913, kind 2, reserved field 0, 1229 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-18006-953080", "unmarked_context_10_18006_953080", "Unmarked parent at depth 10, code 18006",
                "The frontier Boolean is false at remaining fuel 11, original node 953080, the whole prefixCache at depth 10 and code 18006, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-72065-954809", "unmarked_context_11_72065_954809", "Unmarked parent at depth 11, code 72065",
                "The frontier Boolean is false at remaining fuel 10, original node 954809, the whole prefixCache at depth 11 and code 72065, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-18006-953080", "node_context_10_18006_953080", "Original split at fuel 11 and node 953080",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 952878, 952939, 952989, 953079. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-72065-954809", "node_context_11_72065_954809", "Original split at fuel 10 and node 954809",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 34034, 954674, 954728, 954808. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-18005-893098", "context_10_18005_893098", "Context at depth 10, code 18005, node 893098",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18005 and original node 893098, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1153058-954913", "context_13_1153058_954913", "Context at depth 13, code 1153058, node 954913",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1153058 and original node 954913, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
