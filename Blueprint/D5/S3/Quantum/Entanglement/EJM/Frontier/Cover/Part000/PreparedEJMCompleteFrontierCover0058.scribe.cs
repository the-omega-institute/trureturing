using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0058Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0058.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0058",
        H("Original frontier context coverage 0058"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02788", "selected_cut_02788", "Selected cut at depth 12, code 5824, node 86085",
                "At remaining fuel 9 and original index 86085, selection on the full partial prefix of depth 12 and code 5824 returns the complete row with depth 12, base-four code 5824, original node 86085, kind 2, reserved field 0, 1073 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02834", "selected_cut_02834", "Selected cut at depth 14, code 106547, node 87245",
                "At remaining fuel 7 and original index 87245, selection on the full partial prefix of depth 14 and code 106547 returns the complete row with depth 14, base-four code 106547, original node 87245, kind 2, reserved field 0, 1589 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-1455-86071", "unmarked_context_11_1455_86071", "Unmarked parent at depth 11, code 1455",
                "The frontier Boolean is false at remaining fuel 10, original node 86071, the whole prefixCache at depth 11 and code 1455, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-6658-87123", "unmarked_context_12_6658_87123", "Unmarked parent at depth 12, code 6658",
                "The frontier Boolean is false at remaining fuel 9, original node 87123, the whole prefixCache at depth 12 and code 6658, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-1455-86071", "node_context_11_1455_86071", "Original split at fuel 10 and node 86071",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 86033, 86049, 86058, 86070. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-6658-87123", "node_context_12_6658_87123", "Original split at fuel 9 and node 87123",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 86999, 87071, 87112, 87122. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-1455-86071", "context_11_1455_86071", "Context at depth 11, code 1455, node 86071",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 1455 and original node 86071, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_5820_86033, context_12_5821_86049, context_12_5822_86058, context_12_5823_86070.", DescribeRole.Theorem),
            Node("context-14-106547-87245", "context_14_106547_87245", "Context at depth 14, code 106547, node 87245",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 106547 and original node 87245, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
