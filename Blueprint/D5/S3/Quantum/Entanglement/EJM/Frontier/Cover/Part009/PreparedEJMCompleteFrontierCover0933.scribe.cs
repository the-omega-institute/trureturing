using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0933Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0933.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0933",
        H("Original frontier context coverage 0933"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44788", "selected_cut_44788", "Selected cut at depth 12, code 355099, node 1234601",
                "At remaining fuel 9 and original index 1234601, selection on the full partial prefix of depth 12 and code 355099 returns the complete row with depth 12, base-four code 355099, original node 1234601, kind 2, reserved field 0, 3329 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44835", "selected_cut_44835", "Selected cut at depth 11, code 88794, node 900587",
                "At remaining fuel 10 and original index 900587, selection on the full partial prefix of depth 11 and code 88794 returns the complete row with depth 11, base-four code 88794, original node 900587, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88774-1234602", "unmarked_context_11_88774_1234602", "Unmarked parent at depth 11, code 88774",
                "The frontier Boolean is false at remaining fuel 10, original node 1234602, the whole prefixCache at depth 11 and code 88774, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-22196-1235845", "unmarked_context_10_22196_1235845", "Unmarked parent at depth 10, code 22196",
                "The frontier Boolean is false at remaining fuel 11, original node 1235845, the whole prefixCache at depth 10 and code 22196, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88774-1234602", "node_context_11_88774_1234602", "Original split at fuel 10 and node 1234602",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1234442, 1234492, 1234545, 1234601. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-22196-1235845", "node_context_10_22196_1235845", "Original split at fuel 11 and node 1235845",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1235651, 1235720, 1235798, 1235844. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-355099-1234601", "context_12_355099_1234601", "Context at depth 12, code 355099, node 1234601",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 355099 and original node 1234601, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-88794-900587", "context_11_88794_900587", "Context at depth 11, code 88794, node 900587",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88794 and original node 900587, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
