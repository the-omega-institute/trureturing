using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0974Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0974.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0974",
        H("Original frontier context coverage 0974"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46756", "selected_cut_46756", "Selected cut at depth 12, code 371500, node 1305066",
                "At remaining fuel 9 and original index 1305066, selection on the full partial prefix of depth 12 and code 371500 returns the complete row with depth 12, base-four code 371500, original node 1305066, kind 2, reserved field 0, 2521 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46803", "selected_cut_46803", "Selected cut at depth 11, code 92895, node 1306369",
                "At remaining fuel 10 and original index 1306369, selection on the full partial prefix of depth 11 and code 92895 returns the complete row with depth 11, base-four code 92895, original node 1306369, kind 2, reserved field 0, 1909 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92875-1305135", "unmarked_context_11_92875_1305135", "Unmarked parent at depth 11, code 92875",
                "The frontier Boolean is false at remaining fuel 10, original node 1305135, the whole prefixCache at depth 11 and code 92875, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23223-1306370", "unmarked_context_10_23223_1306370", "Unmarked parent at depth 10, code 23223",
                "The frontier Boolean is false at remaining fuel 11, original node 1306370, the whole prefixCache at depth 10 and code 23223, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92875-1305135", "node_context_11_92875_1305135", "Original split at fuel 10 and node 1305135",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1305066, 1305102, 1305134, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23223-1306370", "node_context_10_23223_1306370", "Original split at fuel 11 and node 1306370",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1306245, 1306316, 1306346, 1306369. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-371500-1305066", "context_12_371500_1305066", "Context at depth 12, code 371500, node 1305066",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 371500 and original node 1305066, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-23223-1306370", "context_10_23223_1306370", "Context at depth 10, code 23223, node 1306370",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23223 and original node 1306370, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_92892_1306245, context_11_92893_1306316, context_11_92894_1306346, context_11_92895_1306369.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
