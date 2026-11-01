using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0850Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0850.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0850",
        H("Original frontier context coverage 0850"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40802", "selected_cut_40802", "Selected cut at depth 10, code 20777, node 3442",
                "At remaining fuel 11 and original index 3442, selection on the full partial prefix of depth 10 and code 20777 returns the complete row with depth 10, base-four code 20777, original node 3442, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40849", "selected_cut_40849", "Selected cut at depth 11, code 83227, node 1114186",
                "At remaining fuel 10 and original index 1114186, selection on the full partial prefix of depth 11 and code 83227 returns the complete row with depth 11, base-four code 83227, original node 1114186, kind 2, reserved field 0, 3721 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-20779-1112381", "unmarked_context_10_20779_1112381", "Unmarked parent at depth 10, code 20779",
                "The frontier Boolean is false at remaining fuel 11, original node 1112381, the whole prefixCache at depth 10 and code 20779, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-20806-1114187", "unmarked_context_10_20806_1114187", "Unmarked parent at depth 10, code 20806",
                "The frontier Boolean is false at remaining fuel 11, original node 1114187, the whole prefixCache at depth 10 and code 20806, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-20779-1112381", "node_context_10_20779_1112381", "Original split at fuel 11 and node 1112381",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1112272, 1112326, 1112360, 1112380. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-20806-1114187", "node_context_10_20806_1114187", "Original split at fuel 11 and node 1114187",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1113909, 459416, 1114045, 1114186. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-20777-3442", "context_10_20777_3442", "Context at depth 10, code 20777, node 3442",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 20777 and original node 3442, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-20806-1114187", "context_10_20806_1114187", "Context at depth 10, code 20806, node 1114187",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 20806 and original node 1114187, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_83224_1113909, context_11_83225_459416, context_11_83226_1114045, context_11_83227_1114186.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
