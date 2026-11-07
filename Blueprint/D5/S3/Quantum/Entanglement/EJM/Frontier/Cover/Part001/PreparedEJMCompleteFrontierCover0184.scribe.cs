using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0184Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0184.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0184",
        H("Original frontier context coverage 0184"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08835", "selected_cut_08835", "Selected cut at depth 13, code 92508, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 92508 returns the complete row with depth 13, base-four code 92508, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08883", "selected_cut_08883", "Selected cut at depth 13, code 92574, node 246853",
                "At remaining fuel 8 and original index 246853, selection on the full partial prefix of depth 13 and code 92574 returns the complete row with depth 13, base-four code 92574, original node 246853, kind 2, reserved field 0, 2093 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23127-245977", "unmarked_context_12_23127_245977", "Unmarked parent at depth 12, code 23127",
                "The frontier Boolean is false at remaining fuel 9, original node 245977, the whole prefixCache at depth 12 and code 23127, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5784-246727", "unmarked_context_11_5784_246727", "Unmarked parent at depth 11, code 5784",
                "The frontier Boolean is false at remaining fuel 10, original node 246727, the whole prefixCache at depth 11 and code 5784, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23127-245977", "node_context_12_23127_245977", "Original split at fuel 9 and node 245977",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 245939, 245963, 245976. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5784-246727", "node_context_11_5784_246727", "Original split at fuel 10 and node 246727",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 246563, 246632, 246671, 246726. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-92508-3444", "context_13_92508_3444", "Context at depth 13, code 92508, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92508 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-92574-246853", "context_13_92574_246853", "Context at depth 13, code 92574, node 246853",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92574 and original node 246853, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
