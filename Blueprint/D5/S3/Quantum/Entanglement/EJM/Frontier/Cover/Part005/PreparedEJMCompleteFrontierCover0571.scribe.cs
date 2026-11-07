using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0571Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0571.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0571",
        H("Original frontier context coverage 0571"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27411", "selected_cut_27411", "Selected cut at depth 12, code 91554, node 693005",
                "At remaining fuel 9 and original index 693005, selection on the full partial prefix of depth 12 and code 91554 returns the complete row with depth 12, base-four code 91554, original node 693005, kind 2, reserved field 0, 1401 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27458", "selected_cut_27458", "Selected cut at depth 14, code 1466528, node 694130",
                "At remaining fuel 7 and original index 694130, selection on the full partial prefix of depth 14 and code 1466528 returns the complete row with depth 14, base-four code 1466528, original node 694130, kind 2, reserved field 0, 989 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-22888-693024", "unmarked_context_11_22888_693024", "Unmarked parent at depth 11, code 22888",
                "The frontier Boolean is false at remaining fuel 10, original node 693024, the whole prefixCache at depth 11 and code 22888, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91657-694105", "unmarked_context_12_91657_694105", "Unmarked parent at depth 12, code 91657",
                "The frontier Boolean is false at remaining fuel 9, original node 694105, the whole prefixCache at depth 12 and code 91657, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-22888-693024", "node_context_11_22888_693024", "Original split at fuel 10 and node 693024",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 692974, 692988, 693005, 693023. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91657-694105", "node_context_12_91657_694105", "Original split at fuel 9 and node 694105",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 693987, 694064, 694088, 694104. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-91554-693005", "context_12_91554_693005", "Context at depth 12, code 91554, node 693005",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91554 and original node 693005, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-1466528-694130", "context_14_1466528_694130", "Context at depth 14, code 1466528, node 694130",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 1466528 and original node 694130, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
