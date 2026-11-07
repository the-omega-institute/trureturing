using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0014Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0014.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0014",
        H("Original frontier context coverage 0014"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00674", "selected_cut_00674", "Selected cut at depth 12, code 1580, node 26677",
                "At remaining fuel 9 and original index 26677, selection on the full partial prefix of depth 12 and code 1580 returns the complete row with depth 12, base-four code 1580, original node 26677, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00721", "selected_cut_00721", "Selected cut at depth 13, code 6427, node 29636",
                "At remaining fuel 8 and original index 29636, selection on the full partial prefix of depth 13 and code 6427 returns the complete row with depth 13, base-four code 6427, original node 29636, kind 2, reserved field 0, 1069 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-1581-28740", "unmarked_context_12_1581_28740", "Unmarked parent at depth 12, code 1581",
                "The frontier Boolean is false at remaining fuel 9, original node 28740, the whole prefixCache at depth 12 and code 1581, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-1606-29637", "unmarked_context_12_1606_29637", "Unmarked parent at depth 12, code 1606",
                "The frontier Boolean is false at remaining fuel 9, original node 29637, the whole prefixCache at depth 12 and code 1606, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-1581-28740", "node_context_12_1581_28740", "Original split at fuel 9 and node 28740",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 28667, 28726, 1982, 28739. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-1606-29637", "node_context_12_1606_29637", "Original split at fuel 9 and node 29637",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 29595, 29621, 29636. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-1580-26677", "context_12_1580_26677", "Context at depth 12, code 1580, node 26677",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 1580 and original node 26677, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-1606-29637", "context_12_1606_29637", "Context at depth 12, code 1606, node 29637",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 1606 and original node 29637, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_6424_3444, context_13_6425_29595, context_13_6426_29621, context_13_6427_29636.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
