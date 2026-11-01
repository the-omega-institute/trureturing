using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0615Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0615.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0615",
        H("Original frontier context coverage 0615"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29524", "selected_cut_29524", "Selected cut at depth 12, code 93595, node 745253",
                "At remaining fuel 9 and original index 745253, selection on the full partial prefix of depth 12 and code 93595 returns the complete row with depth 12, base-four code 93595, original node 745253, kind 2, reserved field 0, 1961 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29571", "selected_cut_29571", "Selected cut at depth 13, code 374811, node 746265",
                "At remaining fuel 8 and original index 746265, selection on the full partial prefix of depth 13 and code 374811 returns the complete row with depth 13, base-four code 374811, original node 746265, kind 2, reserved field 0, 1081 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23398-745254", "unmarked_context_11_23398_745254", "Unmarked parent at depth 11, code 23398",
                "The frontier Boolean is false at remaining fuel 10, original node 745254, the whole prefixCache at depth 11 and code 23398, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-365-746105", "unmarked_context_8_365_746105", "Unmarked parent at depth 8, code 365",
                "The frontier Boolean is false at remaining fuel 13, original node 746105, the whole prefixCache at depth 8 and code 365, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23398-745254", "node_context_11_23398_745254", "Original split at fuel 10 and node 745254",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 745176, 745199, 745226, 745253. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-365-746105", "node_context_8_365_746105", "Original split at fuel 13 and node 746105",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 742417, 744494, 745836, 746104. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93595-745253", "context_12_93595_745253", "Context at depth 12, code 93595, node 745253",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93595 and original node 745253, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-374811-746265", "context_13_374811_746265", "Context at depth 13, code 374811, node 746265",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 374811 and original node 746265, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
