using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0048Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0048.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0048",
        H("Original frontier context coverage 0048"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02307", "selected_cut_02307", "Selected cut at depth 13, code 22632, node 75475",
                "At remaining fuel 8 and original index 75475, selection on the full partial prefix of depth 13 and code 22632 returns the complete row with depth 13, base-four code 22632, original node 75475, kind 2, reserved field 0, 3161 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02354", "selected_cut_02354", "Selected cut at depth 13, code 22679, node 76844",
                "At remaining fuel 8 and original index 76844, selection on the full partial prefix of depth 13 and code 22679 returns the complete row with depth 13, base-four code 22679, original node 76844, kind 2, reserved field 0, 1093 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5657-75432", "unmarked_context_12_5657_75432", "Unmarked parent at depth 12, code 5657",
                "The frontier Boolean is false at remaining fuel 9, original node 75432, the whole prefixCache at depth 12 and code 5657, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-5668-76760", "unmarked_context_12_5668_76760", "Unmarked parent at depth 12, code 5668",
                "The frontier Boolean is false at remaining fuel 9, original node 76760, the whole prefixCache at depth 12 and code 5668, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5657-75432", "node_context_12_5657_75432", "Original split at fuel 9 and node 75432",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 75361, 75392, 75418, 75431. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-5668-76760", "node_context_12_5668_76760", "Original split at fuel 9 and node 76760",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 76610, 76673, 76728, 76759. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-5657-75432", "context_12_5657_75432", "Context at depth 12, code 5657, node 75432",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5657 and original node 75432, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_22628_75361, context_13_22629_75392, context_13_22630_75418, context_13_22631_75431.", DescribeRole.Theorem),
            Node("context-13-22679-76844", "context_13_22679_76844", "Context at depth 13, code 22679, node 76844",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22679 and original node 76844, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
