using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0913Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0913.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0913",
        H("Original frontier context coverage 0913"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43826", "selected_cut_43826", "Selected cut at depth 12, code 352580, node 1202066",
                "At remaining fuel 9 and original index 1202066, selection on the full partial prefix of depth 12 and code 352580 returns the complete row with depth 12, base-four code 352580, original node 1202066, kind 2, reserved field 0, 1385 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43874", "selected_cut_43874", "Selected cut at depth 10, code 22046, node 1203331",
                "At remaining fuel 11 and original index 1203331, selection on the full partial prefix of depth 10 and code 22046 returns the complete row with depth 10, base-four code 22046, original node 1203331, kind 2, reserved field 0, 2329 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88145-1202105", "unmarked_context_11_88145_1202105", "Unmarked parent at depth 11, code 88145",
                "The frontier Boolean is false at remaining fuel 10, original node 1202105, the whole prefixCache at depth 11 and code 88145, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-22044-1203232", "unmarked_context_10_22044_1203232", "Unmarked parent at depth 10, code 22044",
                "The frontier Boolean is false at remaining fuel 11, original node 1203232, the whole prefixCache at depth 10 and code 22044, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88145-1202105", "node_context_11_88145_1202105", "Original split at fuel 10 and node 1202105",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1202066, 896706, 1202083, 1202104. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-22044-1203232", "node_context_10_22044_1203232", "Original split at fuel 11 and node 1203232",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 1203193, 1203215, 1203231. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-352580-1202066", "context_12_352580_1202066", "Context at depth 12, code 352580, node 1202066",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 352580 and original node 1202066, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-22046-1203331", "context_10_22046_1203331", "Context at depth 10, code 22046, node 1203331",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22046 and original node 1203331, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
