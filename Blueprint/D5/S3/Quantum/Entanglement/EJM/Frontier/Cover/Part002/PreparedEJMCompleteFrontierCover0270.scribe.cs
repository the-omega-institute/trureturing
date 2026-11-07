using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0270Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0270.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0270",
        H("Original frontier context coverage 0270"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12963", "selected_cut_12963", "Selected cut at depth 13, code 105738, node 341117",
                "At remaining fuel 8 and original index 341117, selection on the full partial prefix of depth 13 and code 105738 returns the complete row with depth 13, base-four code 105738, original node 341117, kind 2, reserved field 0, 2001 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13011", "selected_cut_13011", "Selected cut at depth 13, code 105789, node 342284",
                "At remaining fuel 8 and original index 342284, selection on the full partial prefix of depth 13 and code 105789 returns the complete row with depth 13, base-four code 105789, original node 342284, kind 2, reserved field 0, 3385 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26434-341126", "unmarked_context_12_26434_341126", "Unmarked parent at depth 12, code 26434",
                "The frontier Boolean is false at remaining fuel 9, original node 341126, the whole prefixCache at depth 12 and code 26434, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26446-342213", "unmarked_context_12_26446_342213", "Unmarked parent at depth 12, code 26446",
                "The frontier Boolean is false at remaining fuel 9, original node 342213, the whole prefixCache at depth 12 and code 26446, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26434-341126", "node_context_12_26434_341126", "Original split at fuel 9 and node 341126",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 341088, 341117, 341125. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26446-342213", "node_context_12_26446_342213", "Original split at fuel 9 and node 342213",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 342185, 342206, 342212. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-105738-341117", "context_13_105738_341117", "Context at depth 13, code 105738, node 341117",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105738 and original node 341117, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-105789-342284", "context_13_105789_342284", "Context at depth 13, code 105789, node 342284",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105789 and original node 342284, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
