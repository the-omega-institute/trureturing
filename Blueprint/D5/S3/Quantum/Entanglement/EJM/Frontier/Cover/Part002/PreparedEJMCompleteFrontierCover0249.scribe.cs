using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0249Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0249.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0249",
        H("Original frontier context coverage 0249"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11955", "selected_cut_11955", "Selected cut at depth 13, code 103644, node 318928",
                "At remaining fuel 8 and original index 318928, selection on the full partial prefix of depth 13 and code 103644 returns the complete row with depth 13, base-four code 103644, original node 318928, kind 2, reserved field 0, 565 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12002", "selected_cut_12002", "Selected cut at depth 13, code 103691, node 319768",
                "At remaining fuel 8 and original index 319768, selection on the full partial prefix of depth 13 and code 103691 returns the complete row with depth 13, base-four code 103691, original node 319768, kind 2, reserved field 0, 1049 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25911-318990", "unmarked_context_12_25911_318990", "Unmarked parent at depth 12, code 25911",
                "The frontier Boolean is false at remaining fuel 9, original node 318990, the whole prefixCache at depth 12 and code 25911, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25921-319699", "unmarked_context_12_25921_319699", "Unmarked parent at depth 12, code 25921",
                "The frontier Boolean is false at remaining fuel 9, original node 319699, the whole prefixCache at depth 12 and code 25921, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25911-318990", "node_context_12_25911_318990", "Original split at fuel 9 and node 318990",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 318928, 318961, 318984, 318989. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25921-319699", "node_context_12_25921_319699", "Original split at fuel 9 and node 319699",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 319627, 319686, 319698. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-103644-318928", "context_13_103644_318928", "Context at depth 13, code 103644, node 318928",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 103644 and original node 318928, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-103691-319768", "context_13_103691_319768", "Context at depth 13, code 103691, node 319768",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 103691 and original node 319768, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
