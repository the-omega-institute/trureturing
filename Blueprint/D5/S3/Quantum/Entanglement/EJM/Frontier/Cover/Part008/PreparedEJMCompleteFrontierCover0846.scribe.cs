using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0846Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0846.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0846",
        H("Original frontier context coverage 0846"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40611", "selected_cut_40611", "Selected cut at depth 8, code 1212, node 979897",
                "At remaining fuel 13 and original index 979897, selection on the full partial prefix of depth 8 and code 1212 returns the complete row with depth 8, base-four code 1212, original node 979897, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16777216. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40659", "selected_cut_40659", "Selected cut at depth 12, code 311106, node 1106678",
                "At remaining fuel 9 and original index 1106678, selection on the full partial prefix of depth 12 and code 311106 returns the complete row with depth 12, base-four code 311106, original node 1106678, kind 2, reserved field 0, 2617 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-7-302-1105208", "unmarked_context_7_302_1105208", "Unmarked parent at depth 7, code 302",
                "The frontier Boolean is false at remaining fuel 14, original node 1105208, the whole prefixCache at depth 7 and code 302, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-4860-1106599", "unmarked_context_9_4860_1106599", "Unmarked parent at depth 9, code 4860",
                "The frontier Boolean is false at remaining fuel 12, original node 1106599, the whole prefixCache at depth 9 and code 4860, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-7-302-1105208", "node_context_7_302_1105208", "Original split at fuel 14 and node 1105208",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 979897, 1101012, 979897, 1105207. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-4860-1106599", "node_context_9_4860_1106599", "Original split at fuel 12 and node 1106599",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1105807, 1106287, 1106528, 1106598. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-7-302-1105208", "context_7_302_1105208", "Context at depth 7, code 302, node 1105208",
                "The conclusion is adaptive Accepted at the exact depth 7, full base-four code 302 and original node 1105208, hence remaining fuel 14, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_8_1208_979897, context_8_1209_1101012, context_8_1210_979897, context_8_1211_1105207.", DescribeRole.Theorem),
            Node("context-12-311106-1106678", "context_12_311106_1106678", "Context at depth 12, code 311106, node 1106678",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 311106 and original node 1106678, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
