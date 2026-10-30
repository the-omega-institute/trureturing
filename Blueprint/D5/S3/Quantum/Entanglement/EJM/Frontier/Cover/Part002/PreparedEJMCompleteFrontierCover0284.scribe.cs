using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0284Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0284.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0284",
        H("Original frontier context coverage 0284"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13635", "selected_cut_13635", "Selected cut at depth 11, code 6708, node 356995",
                "At remaining fuel 10 and original index 356995, selection on the full partial prefix of depth 11 and code 6708 returns the complete row with depth 11, base-four code 6708, original node 356995, kind 2, reserved field 0, 3201 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13682", "selected_cut_13682", "Selected cut at depth 13, code 107558, node 358494",
                "At remaining fuel 8 and original index 358494, selection on the full partial prefix of depth 13 and code 107558 returns the complete row with depth 13, base-four code 107558, original node 358494, kind 2, reserved field 0, 2297 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1676-356953", "unmarked_context_10_1676_356953", "Unmarked parent at depth 10, code 1676",
                "The frontier Boolean is false at remaining fuel 11, original node 356953, the whole prefixCache at depth 10 and code 1676, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26888-358394", "unmarked_context_12_26888_358394", "Unmarked parent at depth 12, code 26888",
                "The frontier Boolean is false at remaining fuel 9, original node 358394, the whole prefixCache at depth 12 and code 26888, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1676-356953", "node_context_10_1676_356953", "Original split at fuel 11 and node 356953",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 356864, 356894, 356925, 356952. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26888-358394", "node_context_12_26888_358394", "Original split at fuel 9 and node 358394",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 358256, 358338, 358379, 358393. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-1676-356953", "context_10_1676_356953", "Context at depth 10, code 1676, node 356953",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1676 and original node 356953, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6704_356864, context_11_6705_356894, context_11_6706_356925, context_11_6707_356952.", DescribeRole.Theorem),
            Node("context-13-107558-358494", "context_13_107558_358494", "Context at depth 13, code 107558, node 358494",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 107558 and original node 358494, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
