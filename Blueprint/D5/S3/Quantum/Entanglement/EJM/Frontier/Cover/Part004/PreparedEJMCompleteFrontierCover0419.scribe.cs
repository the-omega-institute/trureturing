using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0419Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0419.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0419",
        H("Original frontier context coverage 0419"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20116", "selected_cut_20116", "Selected cut at depth 13, code 290170, node 514392",
                "At remaining fuel 8 and original index 514392, selection on the full partial prefix of depth 13 and code 290170 returns the complete row with depth 13, base-four code 290170, original node 514392, kind 2, reserved field 0, 1869 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20163", "selected_cut_20163", "Selected cut at depth 12, code 72573, node 516084",
                "At remaining fuel 9 and original index 516084, selection on the full partial prefix of depth 12 and code 72573 returns the complete row with depth 12, base-four code 72573, original node 516084, kind 2, reserved field 0, 2801 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72542-514398", "unmarked_context_12_72542_514398", "Unmarked parent at depth 12, code 72542",
                "The frontier Boolean is false at remaining fuel 9, original node 514398, the whole prefixCache at depth 12 and code 72542, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18142-516020", "unmarked_context_11_18142_516020", "Unmarked parent at depth 11, code 18142",
                "The frontier Boolean is false at remaining fuel 10, original node 516020, the whole prefixCache at depth 11 and code 18142, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72542-514398", "node_context_12_72542_514398", "Original split at fuel 9 and node 514398",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 514369, 514392, 514397. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18142-516020", "node_context_11_18142_516020", "Original split at fuel 10 and node 516020",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 515880, 515927, 515977, 516019. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-290170-514392", "context_13_290170_514392", "Context at depth 13, code 290170, node 514392",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 290170 and original node 514392, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-72573-516084", "context_12_72573_516084", "Context at depth 12, code 72573, node 516084",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72573 and original node 516084, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
