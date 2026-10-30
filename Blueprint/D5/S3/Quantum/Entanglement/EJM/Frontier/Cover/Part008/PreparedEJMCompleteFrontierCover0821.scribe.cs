using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0821Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0821.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0821",
        H("Original frontier context coverage 0821"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39412", "selected_cut_39412", "Selected cut at depth 12, code 302983, node 1069446",
                "At remaining fuel 9 and original index 1069446, selection on the full partial prefix of depth 12 and code 302983 returns the complete row with depth 12, base-four code 302983, original node 1069446, kind 2, reserved field 0, 1325 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39457", "selected_cut_39457", "Selected cut at depth 12, code 307219, node 1070699",
                "At remaining fuel 9 and original index 1070699, selection on the full partial prefix of depth 12 and code 307219 returns the complete row with depth 12, base-four code 307219, original node 1070699, kind 2, reserved field 0, 1937 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75745-1069447", "unmarked_context_11_75745_1069447", "Unmarked parent at depth 11, code 75745",
                "The frontier Boolean is false at remaining fuel 10, original node 1069447, the whole prefixCache at depth 11 and code 75745, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-76804-1070700", "unmarked_context_11_76804_1070700", "Unmarked parent at depth 11, code 76804",
                "The frontier Boolean is false at remaining fuel 10, original node 1070700, the whole prefixCache at depth 11 and code 76804, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75745-1069447", "node_context_11_75745_1069447", "Original split at fuel 10 and node 1069447",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1069405, 1069428, 984676, 1069446. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-76804-1070700", "node_context_11_76804_1070700", "Original split at fuel 10 and node 1070700",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 26677, 1070636, 1070664, 1070699. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-302983-1069446", "context_12_302983_1069446", "Context at depth 12, code 302983, node 1069446",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302983 and original node 1069446, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-76804-1070700", "context_11_76804_1070700", "Context at depth 11, code 76804, node 1070700",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 76804 and original node 1070700, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_307216_26677, context_12_307217_1070636, context_12_307218_1070664, context_12_307219_1070699.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
