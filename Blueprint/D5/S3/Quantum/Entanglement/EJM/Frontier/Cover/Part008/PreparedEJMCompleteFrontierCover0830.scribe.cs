using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0830Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0830.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0830",
        H("Original frontier context coverage 0830"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39843", "selected_cut_39843", "Selected cut at depth 13, code 1231893, node 1081035",
                "At remaining fuel 8 and original index 1081035, selection on the full partial prefix of depth 13 and code 1231893 returns the complete row with depth 13, base-four code 1231893, original node 1081035, kind 2, reserved field 0, 1201 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39891", "selected_cut_39891", "Selected cut at depth 12, code 308010, node 1082724",
                "At remaining fuel 9 and original index 1082724, selection on the full partial prefix of depth 12 and code 308010 returns the complete row with depth 12, base-four code 308010, original node 1082724, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-307973-1081055", "unmarked_context_12_307973_1081055", "Unmarked parent at depth 12, code 307973",
                "The frontier Boolean is false at remaining fuel 9, original node 1081055, the whole prefixCache at depth 12 and code 307973, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-77001-1082625", "unmarked_context_11_77001_1082625", "Unmarked parent at depth 11, code 77001",
                "The frontier Boolean is false at remaining fuel 10, original node 1082625, the whole prefixCache at depth 11 and code 77001, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-307973-1081055", "node_context_12_307973_1081055", "Original split at fuel 9 and node 1081055",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1081014, 1081035, 1081047, 1081054. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-77001-1082625", "node_context_11_77001_1082625", "Original split at fuel 10 and node 1082625",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1082492, 1082544, 1082587, 1082624. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1231893-1081035", "context_13_1231893_1081035", "Context at depth 13, code 1231893, node 1081035",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1231893 and original node 1081035, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-308010-1082724", "context_12_308010_1082724", "Context at depth 12, code 308010, node 1082724",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 308010 and original node 1082724, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
