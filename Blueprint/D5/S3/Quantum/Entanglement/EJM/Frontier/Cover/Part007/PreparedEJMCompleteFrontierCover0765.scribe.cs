using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0765Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0765.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0765",
        H("Original frontier context coverage 0765"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36724", "selected_cut_36724", "Selected cut at depth 13, code 1162255, node 975286",
                "At remaining fuel 8 and original index 975286, selection on the full partial prefix of depth 13 and code 1162255 returns the complete row with depth 13, base-four code 1162255, original node 975286, kind 2, reserved field 0, 561 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36771", "selected_cut_36771", "Selected cut at depth 11, code 72651, node 977678",
                "At remaining fuel 10 and original index 977678, selection on the full partial prefix of depth 11 and code 72651 returns the complete row with depth 11, base-four code 72651, original node 977678, kind 2, reserved field 0, 2225 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-290563-975287", "unmarked_context_12_290563_975287", "Unmarked parent at depth 12, code 290563",
                "The frontier Boolean is false at remaining fuel 9, original node 975287, the whole prefixCache at depth 12 and code 290563, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-72649-977443", "unmarked_context_11_72649_977443", "Unmarked parent at depth 11, code 72649",
                "The frontier Boolean is false at remaining fuel 10, original node 977443, the whole prefixCache at depth 11 and code 72649, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-290563-975287", "node_context_12_290563_975287", "Original split at fuel 9 and node 975287",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 975207, 975235, 975271, 975286. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-72649-977443", "node_context_11_72649_977443", "Original split at fuel 10 and node 977443",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 1738, 977370, 977442. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1162255-975286", "context_13_1162255_975286", "Context at depth 13, code 1162255, node 975286",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1162255 and original node 975286, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-72651-977678", "context_11_72651_977678", "Context at depth 11, code 72651, node 977678",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 72651 and original node 977678, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
