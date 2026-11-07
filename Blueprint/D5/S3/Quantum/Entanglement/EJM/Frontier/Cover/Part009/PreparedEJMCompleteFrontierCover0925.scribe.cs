using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0925Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0925.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0925",
        H("Original frontier context coverage 0925"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44404", "selected_cut_44404", "Selected cut at depth 12, code 354079, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 354079 returns the complete row with depth 12, base-four code 354079, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44451", "selected_cut_44451", "Selected cut at depth 11, code 88539, node 1223079",
                "At remaining fuel 10 and original index 1223079, selection on the full partial prefix of depth 11 and code 88539 returns the complete row with depth 11, base-four code 88539, original node 1223079, kind 2, reserved field 0, 2409 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88519-1221582", "unmarked_context_11_88519_1221582", "Unmarked parent at depth 11, code 88519",
                "The frontier Boolean is false at remaining fuel 10, original node 1221582, the whole prefixCache at depth 11 and code 88519, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88536-1222952", "unmarked_context_11_88536_1222952", "Unmarked parent at depth 11, code 88536",
                "The frontier Boolean is false at remaining fuel 10, original node 1222952, the whole prefixCache at depth 11 and code 88536, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88519-1221582", "node_context_11_88519_1221582", "Original split at fuel 10 and node 1221582",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1221502, 1221529, 1221581, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88536-1222952", "node_context_11_88536_1222952", "Original split at fuel 10 and node 1222952",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1222908, 896706, 1222929, 1222951. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-354079-903806", "context_12_354079_903806", "Context at depth 12, code 354079, node 903806",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 354079 and original node 903806, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-88539-1223079", "context_11_88539_1223079", "Context at depth 11, code 88539, node 1223079",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88539 and original node 1223079, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
