using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0637Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0637.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0637",
        H("Original frontier context coverage 0637"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30580", "selected_cut_30580", "Selected cut at depth 13, code 419023, node 775119",
                "At remaining fuel 8 and original index 775119, selection on the full partial prefix of depth 13 and code 419023 returns the complete row with depth 13, base-four code 419023, original node 775119, kind 2, reserved field 0, 697 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30626", "selected_cut_30626", "Selected cut at depth 13, code 419909, node 777996",
                "At remaining fuel 8 and original index 777996, selection on the full partial prefix of depth 13 and code 419909 returns the complete row with depth 13, base-four code 419909, original node 777996, kind 2, reserved field 0, 2313 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-104755-775120", "unmarked_context_12_104755_775120", "Unmarked parent at depth 12, code 104755",
                "The frontier Boolean is false at remaining fuel 9, original node 775120, the whole prefixCache at depth 12 and code 104755, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-104976-777901", "unmarked_context_12_104976_777901", "Unmarked parent at depth 12, code 104976",
                "The frontier Boolean is false at remaining fuel 9, original node 777901, the whole prefixCache at depth 12 and code 104976, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-104755-775120", "node_context_12_104755_775120", "Original split at fuel 9 and node 775120",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 775002, 775056, 775103, 775119. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-104976-777901", "node_context_12_104976_777901", "Original split at fuel 9 and node 777901",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 777850, 777869, 777888, 777900. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-419023-775119", "context_13_419023_775119", "Context at depth 13, code 419023, node 775119",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 419023 and original node 775119, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-419909-777996", "context_13_419909_777996", "Context at depth 13, code 419909, node 777996",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 419909 and original node 777996, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
