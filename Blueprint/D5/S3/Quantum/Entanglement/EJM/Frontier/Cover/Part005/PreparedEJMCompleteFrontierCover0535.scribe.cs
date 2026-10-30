using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0535Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0535.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0535",
        H("Original frontier context coverage 0535"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25682", "selected_cut_25682", "Selected cut at depth 13, code 352352, node 650925",
                "At remaining fuel 8 and original index 650925, selection on the full partial prefix of depth 13 and code 352352 returns the complete row with depth 13, base-four code 352352, original node 650925, kind 2, reserved field 0, 1145 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25730", "selected_cut_25730", "Selected cut at depth 13, code 352403, node 652030",
                "At remaining fuel 8 and original index 652030, selection on the full partial prefix of depth 13 and code 352403 returns the complete row with depth 13, base-four code 352403, original node 652030, kind 2, reserved field 0, 853 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88088-651002", "unmarked_context_12_88088_651002", "Unmarked parent at depth 12, code 88088",
                "The frontier Boolean is false at remaining fuel 9, original node 651002, the whole prefixCache at depth 12 and code 88088, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22024-651950", "unmarked_context_11_22024_651950", "Unmarked parent at depth 11, code 22024",
                "The frontier Boolean is false at remaining fuel 10, original node 651950, the whole prefixCache at depth 11 and code 22024, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88088-651002", "node_context_12_88088_651002", "Original split at fuel 9 and node 651002",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 650925, 650963, 650995, 651001. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22024-651950", "node_context_11_22024_651950", "Original split at fuel 10 and node 651950",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 355612, 651792, 651871, 651949. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-352352-650925", "context_13_352352_650925", "Context at depth 13, code 352352, node 650925",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 352352 and original node 650925, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-352403-652030", "context_13_352403_652030", "Context at depth 13, code 352403, node 652030",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 352403 and original node 652030, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
