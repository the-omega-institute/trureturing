using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1060Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1060.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1060",
        H("Original frontier context coverage 1060"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50884", "selected_cut_50884", "Selected cut at depth 11, code 110425, node 1459004",
                "At remaining fuel 10 and original index 1459004, selection on the full partial prefix of depth 11 and code 110425 returns the complete row with depth 11, base-four code 110425, original node 1459004, kind 2, reserved field 0, 2065 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50932", "selected_cut_50932", "Selected cut at depth 11, code 110494, node 1460772",
                "At remaining fuel 10 and original index 1460772, selection on the full partial prefix of depth 11 and code 110494 returns the complete row with depth 11, base-four code 110494, original node 1460772, kind 2, reserved field 0, 1205 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-27606-1459039", "unmarked_context_10_27606_1459039", "Unmarked parent at depth 10, code 27606",
                "The frontier Boolean is false at remaining fuel 11, original node 1459039, the whole prefixCache at depth 10 and code 27606, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-27622-1460674", "unmarked_context_10_27622_1460674", "Unmarked parent at depth 10, code 27622",
                "The frontier Boolean is false at remaining fuel 11, original node 1460674, the whole prefixCache at depth 10 and code 27622, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-27606-1459039", "node_context_10_27606_1459039", "Original split at fuel 11 and node 1459039",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1458943, 1459004, 1459005, 1459038. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-27622-1460674", "node_context_10_27622_1460674", "Original split at fuel 11 and node 1460674",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1460568, 1460636, 1459005, 1460673. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-110425-1459004", "context_11_110425_1459004", "Context at depth 11, code 110425, node 1459004",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 110425 and original node 1459004, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-110494-1460772", "context_11_110494_1460772", "Context at depth 11, code 110494, node 1460772",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 110494 and original node 1460772, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
