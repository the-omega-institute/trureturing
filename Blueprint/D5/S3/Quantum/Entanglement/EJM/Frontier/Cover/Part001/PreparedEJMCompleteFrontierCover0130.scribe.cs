using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0130Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0130.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0130",
        H("Original frontier context coverage 0130"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06243", "selected_cut_06243", "Selected cut at depth 12, code 21147, node 187900",
                "At remaining fuel 9 and original index 187900, selection on the full partial prefix of depth 12 and code 21147 returns the complete row with depth 12, base-four code 21147, original node 187900, kind 2, reserved field 0, 2373 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06290", "selected_cut_06290", "Selected cut at depth 11, code 5303, node 188736",
                "At remaining fuel 10 and original index 188736, selection on the full partial prefix of depth 11 and code 5303 returns the complete row with depth 11, base-four code 5303, original node 188736, kind 2, reserved field 0, 1709 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5286-187901", "unmarked_context_11_5286_187901", "Unmarked parent at depth 11, code 5286",
                "The frontier Boolean is false at remaining fuel 10, original node 187901, the whole prefixCache at depth 11 and code 5286, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1324-188647", "unmarked_context_10_1324_188647", "Unmarked parent at depth 10, code 1324",
                "The frontier Boolean is false at remaining fuel 11, original node 188647, the whole prefixCache at depth 10 and code 1324, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5286-187901", "node_context_11_5286_187901", "Original split at fuel 10 and node 187901",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 187807, 187829, 187877, 187900. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1324-188647", "node_context_10_1324_188647", "Original split at fuel 11 and node 188647",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 188551, 188586, 188614, 188646. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-21147-187900", "context_12_21147_187900", "Context at depth 12, code 21147, node 187900",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21147 and original node 187900, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-5303-188736", "context_11_5303_188736", "Context at depth 11, code 5303, node 188736",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5303 and original node 188736, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
