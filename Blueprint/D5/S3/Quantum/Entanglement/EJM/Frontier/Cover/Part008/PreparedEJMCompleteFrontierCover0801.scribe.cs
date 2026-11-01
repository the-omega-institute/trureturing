using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0801Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0801.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0801",
        H("Original frontier context coverage 0801"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38451", "selected_cut_38451", "Selected cut at depth 11, code 75369, node 1036661",
                "At remaining fuel 10 and original index 1036661, selection on the full partial prefix of depth 11 and code 75369 returns the complete row with depth 11, base-four code 75369, original node 1036661, kind 2, reserved field 0, 1641 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38498", "selected_cut_38498", "Selected cut at depth 13, code 1206323, node 1037993",
                "At remaining fuel 8 and original index 1037993, selection on the full partial prefix of depth 13 and code 1206323 returns the complete row with depth 13, base-four code 1206323, original node 1037993, kind 2, reserved field 0, 793 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-18842-1036690", "unmarked_context_10_18842_1036690", "Unmarked parent at depth 10, code 18842",
                "The frontier Boolean is false at remaining fuel 11, original node 1036690, the whole prefixCache at depth 10 and code 18842, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-301580-1037994", "unmarked_context_12_301580_1037994", "Unmarked parent at depth 12, code 301580",
                "The frontier Boolean is false at remaining fuel 9, original node 1037994, the whole prefixCache at depth 12 and code 301580, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-18842-1036690", "node_context_10_18842_1036690", "Original split at fuel 11 and node 1036690",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1036632, 1036661, 906566, 1036689. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-301580-1037994", "node_context_12_301580_1037994", "Original split at fuel 9 and node 1037994",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1037924, 1037953, 1037973, 1037993. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-75369-1036661", "context_11_75369_1036661", "Context at depth 11, code 75369, node 1036661",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75369 and original node 1036661, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-301580-1037994", "context_12_301580_1037994", "Context at depth 12, code 301580, node 1037994",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301580 and original node 1037994, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_1206320_1037924, context_13_1206321_1037953, context_13_1206322_1037973, context_13_1206323_1037993.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
