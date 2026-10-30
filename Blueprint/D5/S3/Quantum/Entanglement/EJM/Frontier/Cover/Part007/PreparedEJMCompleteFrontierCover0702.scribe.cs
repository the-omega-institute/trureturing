using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0702Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0702.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0702",
        H("Original frontier context coverage 0702"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33700", "selected_cut_33700", "Selected cut at depth 13, code 441634, node 867154",
                "At remaining fuel 8 and original index 867154, selection on the full partial prefix of depth 13 and code 441634 returns the complete row with depth 13, base-four code 441634, original node 867154, kind 2, reserved field 0, 1357 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33747", "selected_cut_33747", "Selected cut at depth 12, code 110439, node 868844",
                "At remaining fuel 9 and original index 868844, selection on the full partial prefix of depth 12 and code 110439 returns the complete row with depth 12, base-four code 110439, original node 868844, kind 2, reserved field 0, 3629 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-110408-867160", "unmarked_context_12_110408_867160", "Unmarked parent at depth 12, code 110408",
                "The frontier Boolean is false at remaining fuel 9, original node 867160, the whole prefixCache at depth 12 and code 110408, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27609-868845", "unmarked_context_11_27609_868845", "Unmarked parent at depth 11, code 27609",
                "The frontier Boolean is false at remaining fuel 10, original node 868845, the whole prefixCache at depth 11 and code 27609, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-110408-867160", "node_context_12_110408_867160", "Original split at fuel 9 and node 867160",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 867123, 867154, 867159. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27609-868845", "node_context_11_27609_868845", "Original split at fuel 10 and node 868845",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 868654, 868714, 868779, 868844. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-441634-867154", "context_13_441634_867154", "Context at depth 13, code 441634, node 867154",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 441634 and original node 867154, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-27609-868845", "context_11_27609_868845", "Context at depth 11, code 27609, node 868845",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27609 and original node 868845, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_110436_868654, context_12_110437_868714, context_12_110438_868779, context_12_110439_868844.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
