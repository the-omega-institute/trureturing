using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0439Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0439.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0439",
        H("Original frontier context coverage 0439"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21075", "selected_cut_21075", "Selected cut at depth 12, code 74796, node 540189",
                "At remaining fuel 9 and original index 540189, selection on the full partial prefix of depth 12 and code 74796 returns the complete row with depth 12, base-four code 74796, original node 540189, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21122", "selected_cut_21122", "Selected cut at depth 13, code 299243, node 540905",
                "At remaining fuel 8 and original index 540905, selection on the full partial prefix of depth 13 and code 299243 returns the complete row with depth 13, base-four code 299243, original node 540905, kind 2, reserved field 0, 901 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18698-540188", "unmarked_context_11_18698_540188", "Unmarked parent at depth 11, code 18698",
                "The frontier Boolean is false at remaining fuel 10, original node 540188, the whole prefixCache at depth 11 and code 18698, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-74810-540906", "unmarked_context_12_74810_540906", "Unmarked parent at depth 12, code 74810",
                "The frontier Boolean is false at remaining fuel 9, original node 540906, the whole prefixCache at depth 12 and code 74810, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18698-540188", "node_context_11_18698_540188", "Original split at fuel 10 and node 540188",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 540035, 540104, 540187. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-74810-540906", "node_context_12_74810_540906", "Original split at fuel 9 and node 540906",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 540858, 540882, 540898, 540905. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-18698-540188", "context_11_18698_540188", "Context at depth 11, code 18698, node 540188",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18698 and original node 540188, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_74792_435790, context_12_74793_540035, context_12_74794_540104, context_12_74795_540187.", DescribeRole.Theorem),
            Node("context-12-74810-540906", "context_12_74810_540906", "Context at depth 12, code 74810, node 540906",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 74810 and original node 540906, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_299240_540858, context_13_299241_540882, context_13_299242_540898, context_13_299243_540905.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
