using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0620Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0620.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0620",
        H("Original frontier context coverage 0620"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29765", "selected_cut_29765", "Selected cut at depth 13, code 375023, node 750788",
                "At remaining fuel 8 and original index 750788, selection on the full partial prefix of depth 13 and code 375023 returns the complete row with depth 13, base-four code 375023, original node 750788, kind 2, reserved field 0, 937 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29811", "selected_cut_29811", "Selected cut at depth 12, code 93789, node 642341",
                "At remaining fuel 9 and original index 642341, selection on the full partial prefix of depth 12 and code 93789 returns the complete row with depth 12, base-four code 93789, original node 642341, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93755-750789", "unmarked_context_12_93755_750789", "Unmarked parent at depth 12, code 93755",
                "The frontier Boolean is false at remaining fuel 9, original node 750789, the whole prefixCache at depth 12 and code 93755, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23446-752115", "unmarked_context_11_23446_752115", "Unmarked parent at depth 11, code 23446",
                "The frontier Boolean is false at remaining fuel 10, original node 752115, the whole prefixCache at depth 11 and code 23446, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93755-750789", "node_context_12_93755_750789", "Original split at fuel 9 and node 750789",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 750720, 750760, 750781, 750788. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23446-752115", "node_context_11_23446_752115", "Original split at fuel 10 and node 752115",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 752068, 642341, 290673, 752114. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-375023-750788", "context_13_375023_750788", "Context at depth 13, code 375023, node 750788",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 375023 and original node 750788, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93789-642341", "context_12_93789_642341", "Context at depth 12, code 93789, node 642341",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93789 and original node 642341, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
