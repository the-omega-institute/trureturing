using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0595Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0595.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0595",
        H("Original frontier context coverage 0595"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28563", "selected_cut_28563", "Selected cut at depth 12, code 92502, node 720494",
                "At remaining fuel 9 and original index 720494, selection on the full partial prefix of depth 12 and code 92502 returns the complete row with depth 12, base-four code 92502, original node 720494, kind 2, reserved field 0, 2777 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28610", "selected_cut_28610", "Selected cut at depth 12, code 92549, node 721771",
                "At remaining fuel 9 and original index 721771, selection on the full partial prefix of depth 12 and code 92549 returns the complete row with depth 12, base-four code 92549, original node 721771, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23125-720535", "unmarked_context_11_23125_720535", "Unmarked parent at depth 11, code 23125",
                "The frontier Boolean is false at remaining fuel 10, original node 720535, the whole prefixCache at depth 11 and code 23125, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23136-721742", "unmarked_context_11_23136_721742", "Unmarked parent at depth 11, code 23136",
                "The frontier Boolean is false at remaining fuel 10, original node 721742, the whole prefixCache at depth 11 and code 23136, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23125-720535", "node_context_11_23125_720535", "Original split at fuel 10 and node 720535",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 720455, 642341, 720494, 720534. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23136-721742", "node_context_11_23136_721742", "Original split at fuel 10 and node 721742",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 721657, 721686, 721718, 721741. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-92502-720494", "context_12_92502_720494", "Context at depth 12, code 92502, node 720494",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 92502 and original node 720494, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-92549-721771", "context_12_92549_721771", "Context at depth 12, code 92549, node 721771",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 92549 and original node 721771, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
