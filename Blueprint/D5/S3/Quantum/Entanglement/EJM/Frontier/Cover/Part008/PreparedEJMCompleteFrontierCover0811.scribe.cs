using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0811Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0811.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0811",
        H("Original frontier context coverage 0811"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38932", "selected_cut_38932", "Selected cut at depth 11, code 75568, node 1053825",
                "At remaining fuel 10 and original index 1053825, selection on the full partial prefix of depth 11 and code 75568 returns the complete row with depth 11, base-four code 75568, original node 1053825, kind 2, reserved field 0, 1561 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38978", "selected_cut_38978", "Selected cut at depth 12, code 302372, node 1055797",
                "At remaining fuel 9 and original index 1055797, selection on the full partial prefix of depth 12 and code 302372 returns the complete row with depth 12, base-four code 302372, original node 1055797, kind 2, reserved field 0, 3221 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-18891-1053799", "unmarked_context_10_18891_1053799", "Unmarked parent at depth 10, code 18891",
                "The frontier Boolean is false at remaining fuel 11, original node 1053799, the whole prefixCache at depth 10 and code 18891, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75592-1055746", "unmarked_context_11_75592_1055746", "Unmarked parent at depth 11, code 75592",
                "The frontier Boolean is false at remaining fuel 10, original node 1055746, the whole prefixCache at depth 11 and code 75592, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-18891-1053799", "node_context_10_18891_1053799", "Original split at fuel 11 and node 1053799",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1053710, 1053751, 1053798, 977886. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75592-1055746", "node_context_11_75592_1055746", "Original split at fuel 10 and node 1055746",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1055595, 1055665, 1055702, 1055745. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-18891-1053799", "context_10_18891_1053799", "Context at depth 10, code 18891, node 1053799",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18891 and original node 1053799, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_75564_1053710, context_11_75565_1053751, context_11_75566_1053798, context_11_75567_977886.", DescribeRole.Theorem),
            Node("context-12-302372-1055797", "context_12_302372_1055797", "Context at depth 12, code 302372, node 1055797",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302372 and original node 1055797, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
