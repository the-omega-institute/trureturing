using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0510Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0510.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0510",
        H("Original frontier context coverage 0510"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24484", "selected_cut_24484", "Selected cut at depth 13, code 308623, node 618480",
                "At remaining fuel 8 and original index 618480, selection on the full partial prefix of depth 13 and code 308623 returns the complete row with depth 13, base-four code 308623, original node 618480, kind 2, reserved field 0, 1033 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24530", "selected_cut_24530", "Selected cut at depth 12, code 77195, node 620146",
                "At remaining fuel 9 and original index 620146, selection on the full partial prefix of depth 12 and code 77195 returns the complete row with depth 12, base-four code 77195, original node 620146, kind 2, reserved field 0, 2933 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77155-618481", "unmarked_context_12_77155_618481", "Unmarked parent at depth 12, code 77155",
                "The frontier Boolean is false at remaining fuel 9, original node 618481, the whole prefixCache at depth 12 and code 77155, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19298-620147", "unmarked_context_11_19298_620147", "Unmarked parent at depth 11, code 19298",
                "The frontier Boolean is false at remaining fuel 10, original node 620147, the whole prefixCache at depth 11 and code 19298, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77155-618481", "node_context_12_77155_618481", "Original split at fuel 9 and node 618481",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 618442, 618471, 618480. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19298-620147", "node_context_11_19298_620147", "Original split at fuel 10 and node 620147",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 620027, 620064, 620097, 620146. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-308623-618480", "context_13_308623_618480", "Context at depth 13, code 308623, node 618480",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 308623 and original node 618480, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-19298-620147", "context_11_19298_620147", "Context at depth 11, code 19298, node 620147",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19298 and original node 620147, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_77192_620027, context_12_77193_620064, context_12_77194_620097, context_12_77195_620146.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
