using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0588Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0588.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0588",
        H("Original frontier context coverage 0588"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28228", "selected_cut_28228", "Selected cut at depth 13, code 368764, node 712362",
                "At remaining fuel 8 and original index 712362, selection on the full partial prefix of depth 13 and code 368764 returns the complete row with depth 13, base-four code 368764, original node 712362, kind 2, reserved field 0, 1125 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28275", "selected_cut_28275", "Selected cut at depth 12, code 92223, node 714248",
                "At remaining fuel 9 and original index 714248, selection on the full partial prefix of depth 12 and code 92223 returns the complete row with depth 12, base-four code 92223, original node 714248, kind 2, reserved field 0, 3765 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-92190-712342", "unmarked_context_12_92190_712342", "Unmarked parent at depth 12, code 92190",
                "The frontier Boolean is false at remaining fuel 9, original node 712342, the whole prefixCache at depth 12 and code 92190, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23054-714022", "unmarked_context_11_23054_714022", "Unmarked parent at depth 11, code 23054",
                "The frontier Boolean is false at remaining fuel 10, original node 714022, the whole prefixCache at depth 11 and code 23054, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-92190-712342", "node_context_12_92190_712342", "Original split at fuel 9 and node 712342",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 712295, 712319, 712336, 712341. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23054-714022", "node_context_11_23054_714022", "Original split at fuel 10 and node 714022",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 713837, 713899, 713950, 714021. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-92190-712342", "context_12_92190_712342", "Context at depth 12, code 92190, node 712342",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 92190 and original node 712342, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_368760_712295, context_13_368761_712319, context_13_368762_712336, context_13_368763_712341.", DescribeRole.Theorem),
            Node("context-12-92223-714248", "context_12_92223_714248", "Context at depth 12, code 92223, node 714248",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 92223 and original node 714248, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
