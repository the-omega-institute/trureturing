using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0487Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0487.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0487",
        H("Original frontier context coverage 0487"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23378", "selected_cut_23378", "Selected cut at depth 12, code 76352, node 591763",
                "At remaining fuel 9 and original index 591763, selection on the full partial prefix of depth 12 and code 76352 returns the complete row with depth 12, base-four code 76352, original node 591763, kind 2, reserved field 0, 3857 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23427", "selected_cut_23427", "Selected cut at depth 12, code 76383, node 593242",
                "At remaining fuel 9 and original index 593242, selection on the full partial prefix of depth 12 and code 76383 returns the complete row with depth 12, base-four code 76383, original node 593242, kind 2, reserved field 0, 4089 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76354-591865", "unmarked_context_12_76354_591865", "Unmarked parent at depth 12, code 76354",
                "The frontier Boolean is false at remaining fuel 9, original node 591865, the whole prefixCache at depth 12 and code 76354, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19094-593034", "unmarked_context_11_19094_593034", "Unmarked parent at depth 11, code 19094",
                "The frontier Boolean is false at remaining fuel 10, original node 593034, the whole prefixCache at depth 11 and code 19094, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76354-591865", "node_context_12_76354_591865", "Original split at fuel 9 and node 591865",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 591838, 591857, 591864. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19094-593034", "node_context_11_19094_593034", "Original split at fuel 10 and node 593034",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 592930, 592977, 212113, 593033. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76352-591763", "context_12_76352_591763", "Context at depth 12, code 76352, node 591763",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76352 and original node 591763, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-76383-593242", "context_12_76383_593242", "Context at depth 12, code 76383, node 593242",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76383 and original node 593242, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
