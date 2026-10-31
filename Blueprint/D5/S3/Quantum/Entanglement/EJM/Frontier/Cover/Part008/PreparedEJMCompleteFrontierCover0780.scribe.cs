using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0780Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0780.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0780",
        H("Original frontier context coverage 0780"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37443", "selected_cut_37443", "Selected cut at depth 13, code 1199202, node 1000692",
                "At remaining fuel 8 and original index 1000692, selection on the full partial prefix of depth 13 and code 1199202 returns the complete row with depth 13, base-four code 1199202, original node 1000692, kind 2, reserved field 0, 849 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37491", "selected_cut_37491", "Selected cut at depth 12, code 299838, node 1002724",
                "At remaining fuel 9 and original index 1002724, selection on the full partial prefix of depth 12 and code 299838 returns the complete row with depth 12, base-four code 299838, original node 1002724, kind 2, reserved field 0, 3189 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-299800-1000697", "unmarked_context_12_299800_1000697", "Unmarked parent at depth 12, code 299800",
                "The frontier Boolean is false at remaining fuel 9, original node 1000697, the whole prefixCache at depth 12 and code 299800, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-74958-1002559", "unmarked_context_11_74958_1002559", "Unmarked parent at depth 11, code 74958",
                "The frontier Boolean is false at remaining fuel 10, original node 1002559, the whole prefixCache at depth 11 and code 74958, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-299800-1000697", "node_context_12_299800_1000697", "Original split at fuel 9 and node 1000697",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1000655, 1000673, 1000692, 1000696. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-74958-1002559", "node_context_11_74958_1002559", "Original split at fuel 10 and node 1002559",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1002409, 1002467, 1002512, 1002558. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1199202-1000692", "context_13_1199202_1000692", "Context at depth 13, code 1199202, node 1000692",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1199202 and original node 1000692, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-299838-1002724", "context_12_299838_1002724", "Context at depth 12, code 299838, node 1002724",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299838 and original node 1002724, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
