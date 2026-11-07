using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1055Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1055.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1055",
        H("Original frontier context coverage 1055"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50644", "selected_cut_50644", "Selected cut at depth 11, code 110089, node 1449116",
                "At remaining fuel 10 and original index 1449116, selection on the full partial prefix of depth 11 and code 110089 returns the complete row with depth 11, base-four code 110089, original node 1449116, kind 2, reserved field 0, 3621 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50690", "selected_cut_50690", "Selected cut at depth 12, code 440591, node 1450654",
                "At remaining fuel 9 and original index 1450654, selection on the full partial prefix of depth 12 and code 440591 returns the complete row with depth 12, base-four code 440591, original node 1450654, kind 2, reserved field 0, 2037 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-110088-1449027", "unmarked_context_11_110088_1449027", "Unmarked parent at depth 11, code 110088",
                "The frontier Boolean is false at remaining fuel 10, original node 1449027, the whole prefixCache at depth 11 and code 110088, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-27536-1450656", "unmarked_context_10_27536_1450656", "Unmarked parent at depth 10, code 27536",
                "The frontier Boolean is false at remaining fuel 11, original node 1450656, the whole prefixCache at depth 10 and code 27536, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-110088-1449027", "node_context_11_110088_1449027", "Original split at fuel 10 and node 1449027",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1448897, 1448946, 1448989, 1449026. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-27536-1450656", "node_context_10_27536_1450656", "Original split at fuel 11 and node 1450656",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 434745, 1450523, 1450655. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-110088-1449027", "context_11_110088_1449027", "Context at depth 11, code 110088, node 1449027",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 110088 and original node 1449027, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_440352_1448897, context_12_440353_1448946, context_12_440354_1448989, context_12_440355_1449026.", DescribeRole.Theorem),
            Node("context-10-27536-1450656", "context_10_27536_1450656", "Context at depth 10, code 27536, node 1450656",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 27536 and original node 1450656, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_110144_434745, context_11_110145_434745, context_11_110146_1450523, context_11_110147_1450655.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
