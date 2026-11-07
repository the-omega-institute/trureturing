using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0602Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0602.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0602",
        H("Original frontier context coverage 0602"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28899", "selected_cut_28899", "Selected cut at depth 13, code 372792, node 730209",
                "At remaining fuel 8 and original index 730209, selection on the full partial prefix of depth 13 and code 372792 returns the complete row with depth 13, base-four code 372792, original node 730209, kind 2, reserved field 0, 2865 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28947", "selected_cut_28947", "Selected cut at depth 13, code 372846, node 731427",
                "At remaining fuel 8 and original index 731427, selection on the full partial prefix of depth 13 and code 372846 returns the complete row with depth 13, base-four code 372846, original node 731427, kind 2, reserved field 0, 1881 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93198-730316", "unmarked_context_12_93198_730316", "Unmarked parent at depth 12, code 93198",
                "The frontier Boolean is false at remaining fuel 9, original node 730316, the whole prefixCache at depth 12 and code 93198, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93210-731338", "unmarked_context_12_93210_731338", "Unmarked parent at depth 12, code 93210",
                "The frontier Boolean is false at remaining fuel 9, original node 731338, the whole prefixCache at depth 12 and code 93210, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93198-730316", "node_context_12_93198_730316", "Original split at fuel 9 and node 730316",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 730209, 730279, 730310, 730315. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93210-731338", "node_context_12_93210_731338", "Original split at fuel 9 and node 731338",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 731266, 731300, 731328, 731337. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-372792-730209", "context_13_372792_730209", "Context at depth 13, code 372792, node 730209",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 372792 and original node 730209, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-372846-731427", "context_13_372846_731427", "Context at depth 13, code 372846, node 731427",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 372846 and original node 731427, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
