using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0625Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0625.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0625",
        H("Original frontier context coverage 0625"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30005", "selected_cut_30005", "Selected cut at depth 12, code 93983, node 757807",
                "At remaining fuel 9 and original index 757807, selection on the full partial prefix of depth 12 and code 93983 returns the complete row with depth 12, base-four code 93983, original node 757807, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30052", "selected_cut_30052", "Selected cut at depth 13, code 375982, node 758769",
                "At remaining fuel 8 and original index 758769, selection on the full partial prefix of depth 13 and code 375982 returns the complete row with depth 13, base-four code 375982, original node 758769, kind 2, reserved field 0, 1757 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93982-757806", "unmarked_context_12_93982_757806", "Unmarked parent at depth 12, code 93982",
                "The frontier Boolean is false at remaining fuel 9, original node 757806, the whole prefixCache at depth 12 and code 93982, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93994-758699", "unmarked_context_12_93994_758699", "Unmarked parent at depth 12, code 93994",
                "The frontier Boolean is false at remaining fuel 9, original node 758699, the whole prefixCache at depth 12 and code 93994, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93982-757806", "node_context_12_93982_757806", "Original split at fuel 9 and node 757806",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 757747, 757782, 757800, 757805. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93994-758699", "node_context_12_93994_758699", "Original split at fuel 9 and node 758699",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 758646, 758673, 758693, 758698. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93982-757806", "context_12_93982_757806", "Context at depth 12, code 93982, node 757806",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93982 and original node 757806, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_375928_757747, context_13_375929_757782, context_13_375930_757800, context_13_375931_757805.", DescribeRole.Theorem),
            Node("context-13-375982-758769", "context_13_375982_758769", "Context at depth 13, code 375982, node 758769",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 375982 and original node 758769, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
