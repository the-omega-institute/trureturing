using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0557Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0557.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0557",
        H("Original frontier context coverage 0557"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26740", "selected_cut_26740", "Selected cut at depth 12, code 88990, node 676056",
                "At remaining fuel 9 and original index 676056, selection on the full partial prefix of depth 12 and code 88990 returns the complete row with depth 12, base-four code 88990, original node 676056, kind 2, reserved field 0, 1537 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26786", "selected_cut_26786", "Selected cut at depth 13, code 364574, node 676993",
                "At remaining fuel 8 and original index 676993, selection on the full partial prefix of depth 13 and code 364574 returns the complete row with depth 13, base-four code 364574, original node 676993, kind 2, reserved field 0, 713 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-22247-676076", "unmarked_context_11_22247_676076", "Unmarked parent at depth 11, code 22247",
                "The frontier Boolean is false at remaining fuel 10, original node 676076, the whole prefixCache at depth 11 and code 22247, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91142-676865", "unmarked_context_12_91142_676865", "Unmarked parent at depth 12, code 91142",
                "The frontier Boolean is false at remaining fuel 9, original node 676865, the whole prefixCache at depth 12 and code 91142, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-22247-676076", "node_context_11_22247_676076", "Original split at fuel 10 and node 676076",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 676021, 676038, 676056, 676075. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91142-676865", "node_context_12_91142_676865", "Original split at fuel 9 and node 676865",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 676806, 676849, 676862, 676864. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-88990-676056", "context_12_88990_676056", "Context at depth 12, code 88990, node 676056",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88990 and original node 676056, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-364574-676993", "context_13_364574_676993", "Context at depth 13, code 364574, node 676993",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 364574 and original node 676993, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
