using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0806Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0806.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0806",
        H("Original frontier context coverage 0806"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38692", "selected_cut_38692", "Selected cut at depth 12, code 301879, node 1045484",
                "At remaining fuel 9 and original index 1045484, selection on the full partial prefix of depth 12 and code 301879 returns the complete row with depth 12, base-four code 301879, original node 1045484, kind 2, reserved field 0, 2821 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38739", "selected_cut_38739", "Selected cut at depth 12, code 301944, node 1047071",
                "At remaining fuel 9 and original index 1047071, selection on the full partial prefix of depth 12 and code 301944 returns the complete row with depth 12, base-four code 301944, original node 1047071, kind 2, reserved field 0, 1761 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75469-1045485", "unmarked_context_11_75469_1045485", "Unmarked parent at depth 11, code 75469",
                "The frontier Boolean is false at remaining fuel 10, original node 1045485, the whole prefixCache at depth 11 and code 75469, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75485-1047043", "unmarked_context_11_75485_1047043", "Unmarked parent at depth 11, code 75485",
                "The frontier Boolean is false at remaining fuel 10, original node 1047043, the whole prefixCache at depth 11 and code 75485, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75469-1045485", "node_context_11_75469_1045485", "Original split at fuel 10 and node 1045485",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1045313, 1045378, 1045436, 1045484. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75485-1047043", "node_context_11_75485_1047043", "Original split at fuel 10 and node 1047043",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1046981, 1046982, 1047019, 1047042. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-301879-1045484", "context_12_301879_1045484", "Context at depth 12, code 301879, node 1045484",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301879 and original node 1045484, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-301944-1047071", "context_12_301944_1047071", "Context at depth 12, code 301944, node 1047071",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301944 and original node 1047071, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
