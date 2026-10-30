using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0434Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0434.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0434",
        H("Original frontier context coverage 0434"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20835", "selected_cut_20835", "Selected cut at depth 13, code 298119, node 533194",
                "At remaining fuel 8 and original index 533194, selection on the full partial prefix of depth 13 and code 298119 returns the complete row with depth 13, base-four code 298119, original node 533194, kind 2, reserved field 0, 577 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20882", "selected_cut_20882", "Selected cut at depth 13, code 298196, node 534553",
                "At remaining fuel 8 and original index 534553, selection on the full partial prefix of depth 13 and code 298196 returns the complete row with depth 13, base-four code 298196, original node 534553, kind 2, reserved field 0, 329 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-74529-533195", "unmarked_context_12_74529_533195", "Unmarked parent at depth 12, code 74529",
                "The frontier Boolean is false at remaining fuel 9, original node 533195, the whole prefixCache at depth 12 and code 74529, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-74548-534546", "unmarked_context_12_74548_534546", "Unmarked parent at depth 12, code 74548",
                "The frontier Boolean is false at remaining fuel 9, original node 534546, the whole prefixCache at depth 12 and code 74548, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-74529-533195", "node_context_12_74529_533195", "Original split at fuel 9 and node 533195",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 533140, 533173, 533189, 533194. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-74548-534546", "node_context_12_74548_534546", "Original split at fuel 9 and node 534546",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 534449, 534493, 534526, 534545. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-298119-533194", "context_13_298119_533194", "Context at depth 13, code 298119, node 533194",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 298119 and original node 533194, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-298196-534553", "context_13_298196_534553", "Context at depth 13, code 298196, node 534553",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 298196 and original node 534553, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
