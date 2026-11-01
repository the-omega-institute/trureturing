using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0903Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0903.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0903",
        H("Original frontier context coverage 0903"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 45 exact cut-selection equations, and 19 literal split equations paired with 19 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43349", "selected_cut_43349", "Selected cut at depth 11, code 84959, node 977886",
                "At remaining fuel 10 and original index 977886, selection on the full partial prefix of depth 11 and code 84959 returns the complete row with depth 11, base-four code 84959, original node 977886, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43393", "selected_cut_43393", "Selected cut at depth 11, code 87427, node 1187230",
                "At remaining fuel 10 and original index 1187230, selection on the full partial prefix of depth 11 and code 87427 returns the complete row with depth 11, base-four code 87427, original node 1187230, kind 2, reserved field 0, 1537 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84958-1186043", "unmarked_context_11_84958_1186043", "Unmarked parent at depth 11, code 84958",
                "The frontier Boolean is false at remaining fuel 10, original node 1186043, the whole prefixCache at depth 11 and code 84958, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21856-1187231", "unmarked_context_10_21856_1187231", "Unmarked parent at depth 10, code 21856",
                "The frontier Boolean is false at remaining fuel 11, original node 1187231, the whole prefixCache at depth 10 and code 21856, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84958-1186043", "node_context_11_84958_1186043", "Original split at fuel 10 and node 1186043",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1185985, 1186005, 1186027, 1186042. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21856-1187231", "node_context_10_21856_1187231", "Original split at fuel 11 and node 1187231",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 1187129, 1187186, 1187230. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84958-1186043", "context_11_84958_1186043", "Context at depth 11, code 84958, node 1186043",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84958 and original node 1186043, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_339832_1185985, context_12_339833_1186005, context_12_339834_1186027, context_12_339835_1186042.", DescribeRole.Theorem),
            Node("context-10-21856-1187231", "context_10_21856_1187231", "Context at depth 10, code 21856, node 1187231",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21856 and original node 1187231, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_87424_434745, context_11_87425_1187129, context_11_87426_1187186, context_11_87427_1187230.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
