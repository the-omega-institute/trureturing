using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0709Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0709.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0709",
        H("Original frontier context coverage 0709"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34036", "selected_cut_34036", "Selected cut at depth 13, code 451684, node 879268",
                "At remaining fuel 8 and original index 879268, selection on the full partial prefix of depth 13 and code 451684 returns the complete row with depth 13, base-four code 451684, original node 879268, kind 2, reserved field 0, 1485 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34083", "selected_cut_34083", "Selected cut at depth 13, code 451737, node 880142",
                "At remaining fuel 8 and original index 880142, selection on the full partial prefix of depth 13 and code 451737 returns the complete row with depth 13, base-four code 451737, original node 880142, kind 2, reserved field 0, 1705 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-112920-879248", "unmarked_context_12_112920_879248", "Unmarked parent at depth 12, code 112920",
                "The frontier Boolean is false at remaining fuel 9, original node 879248, the whole prefixCache at depth 12 and code 112920, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-28232-880048", "unmarked_context_11_28232_880048", "Unmarked parent at depth 11, code 28232",
                "The frontier Boolean is false at remaining fuel 10, original node 880048, the whole prefixCache at depth 11 and code 28232, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-112920-879248", "node_context_12_112920_879248", "Original split at fuel 9 and node 879248",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 879202, 879223, 879243, 879247. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-28232-880048", "node_context_11_28232_880048", "Original split at fuel 10 and node 880048",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 879852, 879919, 879985, 880047. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-112920-879248", "context_12_112920_879248", "Context at depth 12, code 112920, node 879248",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 112920 and original node 879248, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_451680_879202, context_13_451681_879223, context_13_451682_879243, context_13_451683_879247.", DescribeRole.Theorem),
            Node("context-13-451737-880142", "context_13_451737_880142", "Context at depth 13, code 451737, node 880142",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 451737 and original node 880142, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
