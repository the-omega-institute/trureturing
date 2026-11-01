using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0313Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0313.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0313",
        H("Original frontier context coverage 0313"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15028", "selected_cut_15028", "Selected cut at depth 12, code 27502, node 386413",
                "At remaining fuel 9 and original index 386413, selection on the full partial prefix of depth 12 and code 27502 returns the complete row with depth 12, base-four code 27502, original node 386413, kind 2, reserved field 0, 2885 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15075", "selected_cut_15075", "Selected cut at depth 12, code 27543, node 387901",
                "At remaining fuel 9 and original index 387901, selection on the full partial prefix of depth 12 and code 27543 returns the complete row with depth 12, base-four code 27543, original node 387901, kind 2, reserved field 0, 2053 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27503-386508", "unmarked_context_12_27503_386508", "Unmarked parent at depth 12, code 27503",
                "The frontier Boolean is false at remaining fuel 9, original node 386508, the whole prefixCache at depth 12 and code 27503, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6884-387813", "unmarked_context_11_6884_387813", "Unmarked parent at depth 11, code 6884",
                "The frontier Boolean is false at remaining fuel 10, original node 387813, the whole prefixCache at depth 11 and code 6884, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27503-386508", "node_context_12_27503_386508", "Original split at fuel 9 and node 386508",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 386440, 386483, 386507. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6884-387813", "node_context_11_6884_387813", "Original split at fuel 10 and node 387813",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 387743, 387764, 387790, 387812. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-27502-386413", "context_12_27502_386413", "Context at depth 12, code 27502, node 386413",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27502 and original node 386413, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27543-387901", "context_12_27543_387901", "Context at depth 12, code 27543, node 387901",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27543 and original node 387901, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
