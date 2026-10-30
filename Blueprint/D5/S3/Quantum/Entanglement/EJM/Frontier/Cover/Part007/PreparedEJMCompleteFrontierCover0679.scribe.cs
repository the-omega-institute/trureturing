using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0679Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0679.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0679",
        H("Original frontier context coverage 0679"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32596", "selected_cut_32596", "Selected cut at depth 13, code 438424, node 838819",
                "At remaining fuel 8 and original index 838819, selection on the full partial prefix of depth 13 and code 438424 returns the complete row with depth 13, base-four code 438424, original node 838819, kind 2, reserved field 0, 1157 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32643", "selected_cut_32643", "Selected cut at depth 13, code 438474, node 839844",
                "At remaining fuel 8 and original index 839844, selection on the full partial prefix of depth 13 and code 438474 returns the complete row with depth 13, base-four code 438474, original node 839844, kind 2, reserved field 0, 825 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-109605-838797", "unmarked_context_12_109605_838797", "Unmarked parent at depth 12, code 109605",
                "The frontier Boolean is false at remaining fuel 9, original node 838797, the whole prefixCache at depth 12 and code 109605, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-109617-839791", "unmarked_context_12_109617_839791", "Unmarked parent at depth 12, code 109617",
                "The frontier Boolean is false at remaining fuel 9, original node 839791, the whole prefixCache at depth 12 and code 109617, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-109605-838797", "node_context_12_109605_838797", "Original split at fuel 9 and node 838797",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 838713, 838753, 838788, 838796. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-109617-839791", "node_context_12_109617_839791", "Original split at fuel 9 and node 839791",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 839734, 839762, 839784, 839790. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-109605-838797", "context_12_109605_838797", "Context at depth 12, code 109605, node 838797",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109605 and original node 838797, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_438420_838713, context_13_438421_838753, context_13_438422_838788, context_13_438423_838796.", DescribeRole.Theorem),
            Node("context-13-438474-839844", "context_13_438474_839844", "Context at depth 13, code 438474, node 839844",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 438474 and original node 839844, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
