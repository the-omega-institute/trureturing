using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0666Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0666.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0666",
        H("Original frontier context coverage 0666"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31972", "selected_cut_31972", "Selected cut at depth 12, code 107788, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 107788 returns the complete row with depth 12, base-four code 107788, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32019", "selected_cut_32019", "Selected cut at depth 13, code 431223, node 822736",
                "At remaining fuel 8 and original index 822736, selection on the full partial prefix of depth 13 and code 431223 returns the complete row with depth 13, base-four code 431223, original node 822736, kind 2, reserved field 0, 765 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-107787-821556", "unmarked_context_12_107787_821556", "Unmarked parent at depth 12, code 107787",
                "The frontier Boolean is false at remaining fuel 9, original node 821556, the whole prefixCache at depth 12 and code 107787, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-107804-822648", "unmarked_context_12_107804_822648", "Unmarked parent at depth 12, code 107804",
                "The frontier Boolean is false at remaining fuel 9, original node 822648, the whole prefixCache at depth 12 and code 107804, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-107787-821556", "node_context_12_107787_821556", "Original split at fuel 9 and node 821556",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 821328, 821417, 821520, 821555. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-107804-822648", "node_context_12_107804_822648", "Original split at fuel 9 and node 822648",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 822555, 822616, 822639, 822647. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-107787-821556", "context_12_107787_821556", "Context at depth 12, code 107787, node 821556",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 107787 and original node 821556, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_431148_821328, context_13_431149_821417, context_13_431150_821520, context_13_431151_821555.", DescribeRole.Theorem),
            Node("context-13-431223-822736", "context_13_431223_822736", "Context at depth 13, code 431223, node 822736",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 431223 and original node 822736, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
