using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0150Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0150.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0150",
        H("Original frontier context coverage 0150"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07203", "selected_cut_07203", "Selected cut at depth 13, code 88470, node 209791",
                "At remaining fuel 8 and original index 209791, selection on the full partial prefix of depth 13 and code 88470 returns the complete row with depth 13, base-four code 88470, original node 209791, kind 2, reserved field 0, 2105 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07249", "selected_cut_07249", "Selected cut at depth 12, code 22147, node 211116",
                "At remaining fuel 9 and original index 211116, selection on the full partial prefix of depth 12 and code 22147 returns the complete row with depth 12, base-four code 22147, original node 211116, kind 2, reserved field 0, 2341 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22117-209802", "unmarked_context_12_22117_209802", "Unmarked parent at depth 12, code 22117",
                "The frontier Boolean is false at remaining fuel 9, original node 209802, the whole prefixCache at depth 12 and code 22117, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5536-211117", "unmarked_context_11_5536_211117", "Unmarked parent at depth 11, code 5536",
                "The frontier Boolean is false at remaining fuel 10, original node 211117, the whole prefixCache at depth 11 and code 5536, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22117-209802", "node_context_12_22117_209802", "Original split at fuel 9 and node 209802",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 209762, 209791, 209801. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5536-211117", "node_context_11_5536_211117", "Original split at fuel 10 and node 211117",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 211023, 211054, 211084, 211116. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-88470-209791", "context_13_88470_209791", "Context at depth 13, code 88470, node 209791",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88470 and original node 209791, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-5536-211117", "context_11_5536_211117", "Context at depth 11, code 5536, node 211117",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5536 and original node 211117, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_22144_211023, context_12_22145_211054, context_12_22146_211084, context_12_22147_211116.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
