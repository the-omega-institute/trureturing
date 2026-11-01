using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0243Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0243.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0243",
        H("Original frontier context coverage 0243"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11666", "selected_cut_11666", "Selected cut at depth 12, code 25748, node 312001",
                "At remaining fuel 9 and original index 312001, selection on the full partial prefix of depth 12 and code 25748 returns the complete row with depth 12, base-four code 25748, original node 312001, kind 2, reserved field 0, 2681 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11714", "selected_cut_11714", "Selected cut at depth 11, code 6455, node 313207",
                "At remaining fuel 10 and original index 313207, selection on the full partial prefix of depth 11 and code 6455 returns the complete row with depth 11, base-four code 6455, original node 313207, kind 2, reserved field 0, 1801 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6437-312120", "unmarked_context_11_6437_312120", "Unmarked parent at depth 11, code 6437",
                "The frontier Boolean is false at remaining fuel 10, original node 312120, the whole prefixCache at depth 11 and code 6437, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1612-313105", "unmarked_context_10_1612_313105", "Unmarked parent at depth 10, code 1612",
                "The frontier Boolean is false at remaining fuel 11, original node 313105, the whole prefixCache at depth 10 and code 1612, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6437-312120", "node_context_11_6437_312120", "Original split at fuel 10 and node 312120",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 312001, 312048, 312079, 312119. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1612-313105", "node_context_10_1612_313105", "Original split at fuel 11 and node 313105",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 312988, 313024, 313070, 313104. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25748-312001", "context_12_25748_312001", "Context at depth 12, code 25748, node 312001",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25748 and original node 312001, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-6455-313207", "context_11_6455_313207", "Context at depth 11, code 6455, node 313207",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6455 and original node 313207, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
