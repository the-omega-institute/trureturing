using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1092Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1092.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1092",
        H("Original frontier context coverage 1092"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52419", "selected_cut_52419", "Selected cut at depth 11, code 289668, node 1528179",
                "At remaining fuel 10 and original index 1528179, selection on the full partial prefix of depth 11 and code 289668 returns the complete row with depth 11, base-four code 289668, original node 1528179, kind 2, reserved field 0, 1641 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52466", "selected_cut_52466", "Selected cut at depth 10, code 72467, node 1530644",
                "At remaining fuel 11 and original index 1530644, selection on the full partial prefix of depth 10 and code 72467 returns the complete row with depth 10, base-four code 72467, original node 1530644, kind 2, reserved field 0, 3493 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-72417-1528371", "unmarked_context_10_72417_1528371", "Unmarked parent at depth 10, code 72417",
                "The frontier Boolean is false at remaining fuel 11, original node 1528371, the whole prefixCache at depth 10 and code 72417, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-72465-1530449", "unmarked_context_10_72465_1530449", "Unmarked parent at depth 10, code 72465",
                "The frontier Boolean is false at remaining fuel 11, original node 1530449, the whole prefixCache at depth 10 and code 72465, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-72417-1528371", "node_context_10_72417_1528371", "Original split at fuel 11 and node 1528371",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1528179, 1468419, 1528278, 1528370. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-72465-1530449", "node_context_10_72465_1530449", "Original split at fuel 11 and node 1530449",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1530334, 1468419, 1530370, 1530448. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-289668-1528179", "context_11_289668_1528179", "Context at depth 11, code 289668, node 1528179",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 289668 and original node 1528179, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-72467-1530644", "context_10_72467_1530644", "Context at depth 10, code 72467, node 1530644",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 72467 and original node 1530644, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
