using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0932Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0932.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0932",
        H("Original frontier context coverage 0932"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44740", "selected_cut_44740", "Selected cut at depth 11, code 88732, node 1232863",
                "At remaining fuel 10 and original index 1232863, selection on the full partial prefix of depth 11 and code 88732 returns the complete row with depth 11, base-four code 88732, original node 1232863, kind 2, reserved field 0, 3753 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44787", "selected_cut_44787", "Selected cut at depth 12, code 355098, node 1234545",
                "At remaining fuel 9 and original index 1234545, selection on the full partial prefix of depth 12 and code 355098 returns the complete row with depth 12, base-four code 355098, original node 1234545, kind 2, reserved field 0, 2925 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22182-1232789", "unmarked_context_10_22182_1232789", "Unmarked parent at depth 10, code 22182",
                "The frontier Boolean is false at remaining fuel 11, original node 1232789, the whole prefixCache at depth 10 and code 22182, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88773-1234390", "unmarked_context_11_88773_1234390", "Unmarked parent at depth 11, code 88773",
                "The frontier Boolean is false at remaining fuel 10, original node 1234390, the whole prefixCache at depth 11 and code 88773, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22182-1232789", "node_context_10_22182_1232789", "Original split at fuel 11 and node 1232789",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1232669, 1232728, 900587, 1232788. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88773-1234390", "node_context_11_88773_1234390", "Original split at fuel 10 and node 1234390",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 1118965, 1234330, 1234389. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-22182-1232789", "context_10_22182_1232789", "Context at depth 10, code 22182, node 1232789",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22182 and original node 1232789, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_88728_1232669, context_11_88729_1232728, context_11_88730_900587, context_11_88731_1232788.", DescribeRole.Theorem),
            Node("context-12-355098-1234545", "context_12_355098_1234545", "Context at depth 12, code 355098, node 1234545",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 355098 and original node 1234545, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
