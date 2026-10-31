using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0828Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0828.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0828",
        H("Original frontier context coverage 0828"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39747", "selected_cut_39747", "Selected cut at depth 12, code 307761, node 1078414",
                "At remaining fuel 9 and original index 1078414, selection on the full partial prefix of depth 12 and code 307761 returns the complete row with depth 12, base-four code 307761, original node 1078414, kind 2, reserved field 0, 2857 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39795", "selected_cut_39795", "Selected cut at depth 12, code 307827, node 1079912",
                "At remaining fuel 9 and original index 1079912, selection on the full partial prefix of depth 12 and code 307827 returns the complete row with depth 12, base-four code 307827, original node 1079912, kind 2, reserved field 0, 1569 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-76940-1078517", "unmarked_context_11_76940_1078517", "Unmarked parent at depth 11, code 76940",
                "The frontier Boolean is false at remaining fuel 10, original node 1078517, the whole prefixCache at depth 11 and code 76940, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-19238-1079825", "unmarked_context_10_19238_1079825", "Unmarked parent at depth 10, code 19238",
                "The frontier Boolean is false at remaining fuel 11, original node 1079825, the whole prefixCache at depth 10 and code 19238, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-76940-1078517", "node_context_11_76940_1078517", "Original split at fuel 10 and node 1078517",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994572, 1078414, 1078465, 1078516. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-19238-1079825", "node_context_10_19238_1079825", "Original split at fuel 11 and node 1079825",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1079532, 1079611, 1079696, 1079824. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-307761-1078414", "context_12_307761_1078414", "Context at depth 12, code 307761, node 1078414",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 307761 and original node 1078414, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-307827-1079912", "context_12_307827_1079912", "Context at depth 12, code 307827, node 1079912",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 307827 and original node 1079912, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
