using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0466Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0466.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0466",
        H("Original frontier context coverage 0466"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22372", "selected_cut_22372", "Selected cut at depth 13, code 302398, node 569264",
                "At remaining fuel 8 and original index 569264, selection on the full partial prefix of depth 13 and code 302398 returns the complete row with depth 13, base-four code 302398, original node 569264, kind 2, reserved field 0, 2677 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22418", "selected_cut_22418", "Selected cut at depth 12, code 75617, node 570191",
                "At remaining fuel 9 and original index 570191, selection on the full partial prefix of depth 12 and code 75617 returns the complete row with depth 12, base-four code 75617, original node 570191, kind 2, reserved field 0, 3949 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75599-569275", "unmarked_context_12_75599_569275", "Unmarked parent at depth 12, code 75599",
                "The frontier Boolean is false at remaining fuel 9, original node 569275, the whole prefixCache at depth 12 and code 75599, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4725-570093", "unmarked_context_10_4725_570093", "Unmarked parent at depth 10, code 4725",
                "The frontier Boolean is false at remaining fuel 11, original node 570093, the whole prefixCache at depth 10 and code 4725, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75599-569275", "node_context_12_75599_569275", "Original split at fuel 9 and node 569275",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 569214, 569264, 569274. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4725-570093", "node_context_10_4725_570093", "Original split at fuel 11 and node 570093",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 569553, 451541, 569807, 570092. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-302398-569264", "context_13_302398_569264", "Context at depth 13, code 302398, node 569264",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302398 and original node 569264, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-75617-570191", "context_12_75617_570191", "Context at depth 12, code 75617, node 570191",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75617 and original node 570191, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
