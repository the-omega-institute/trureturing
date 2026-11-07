using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0106Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0106.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0106",
        H("Original frontier context coverage 0106"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05091", "selected_cut_05091", "Selected cut at depth 11, code 4731, node 158323",
                "At remaining fuel 10 and original index 158323, selection on the full partial prefix of depth 11 and code 4731 returns the complete row with depth 11, base-four code 4731, original node 158323, kind 2, reserved field 0, 961 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05138", "selected_cut_05138", "Selected cut at depth 13, code 76847, node 159848",
                "At remaining fuel 8 and original index 159848, selection on the full partial prefix of depth 13 and code 76847 returns the complete row with depth 13, base-four code 76847, original node 159848, kind 2, reserved field 0, 913 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1182-158324", "unmarked_context_10_1182_158324", "Unmarked parent at depth 10, code 1182",
                "The frontier Boolean is false at remaining fuel 11, original node 158324, the whole prefixCache at depth 10 and code 1182, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-19211-159849", "unmarked_context_12_19211_159849", "Unmarked parent at depth 12, code 19211",
                "The frontier Boolean is false at remaining fuel 9, original node 159849, the whole prefixCache at depth 12 and code 19211, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1182-158324", "node_context_10_1182_158324", "Original split at fuel 11 and node 158324",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 158267, 158287, 158307, 158323. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-19211-159849", "node_context_12_19211_159849", "Original split at fuel 9 and node 159849",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 159753, 159814, 159839, 159848. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-4731-158323", "context_11_4731_158323", "Context at depth 11, code 4731, node 158323",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 4731 and original node 158323, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-19211-159849", "context_12_19211_159849", "Context at depth 12, code 19211, node 159849",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 19211 and original node 159849, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_76844_159753, context_13_76845_159814, context_13_76846_159839, context_13_76847_159848.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
