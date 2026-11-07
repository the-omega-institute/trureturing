using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0629Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0629.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0629",
        H("Original frontier context coverage 0629"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30196", "selected_cut_30196", "Selected cut at depth 12, code 94087, node 762316",
                "At remaining fuel 9 and original index 762316, selection on the full partial prefix of depth 12 and code 94087 returns the complete row with depth 12, base-four code 94087, original node 762316, kind 2, reserved field 0, 2501 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30244", "selected_cut_30244", "Selected cut at depth 12, code 94138, node 763285",
                "At remaining fuel 9 and original index 763285, selection on the full partial prefix of depth 12 and code 94138 returns the complete row with depth 12, base-four code 94138, original node 763285, kind 2, reserved field 0, 1029 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23521-762317", "unmarked_context_11_23521_762317", "Unmarked parent at depth 11, code 23521",
                "The frontier Boolean is false at remaining fuel 10, original node 762317, the whole prefixCache at depth 11 and code 23521, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23533-763254", "unmarked_context_11_23533_763254", "Unmarked parent at depth 11, code 23533",
                "The frontier Boolean is false at remaining fuel 10, original node 763254, the whole prefixCache at depth 11 and code 23533, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23521-762317", "node_context_11_23521_762317", "Original split at fuel 10 and node 762317",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 762243, 762269, 762289, 762316. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23533-763254", "node_context_11_23533_763254", "Original split at fuel 10 and node 763254",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 763216, 763227, 763241, 763253. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-94087-762316", "context_12_94087_762316", "Context at depth 12, code 94087, node 762316",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 94087 and original node 762316, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-94138-763285", "context_12_94138_763285", "Context at depth 12, code 94138, node 763285",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 94138 and original node 763285, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
