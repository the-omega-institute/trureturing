using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0095Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0095.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0095",
        H("Original frontier context coverage 0095"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04562", "selected_cut_04562", "Selected cut at depth 13, code 74768, node 147538",
                "At remaining fuel 8 and original index 147538, selection on the full partial prefix of depth 13 and code 74768 returns the complete row with depth 13, base-four code 74768, original node 147538, kind 2, reserved field 0, 3477 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04609", "selected_cut_04609", "Selected cut at depth 13, code 74800, node 148899",
                "At remaining fuel 8 and original index 148899, selection on the full partial prefix of depth 13 and code 74800 returns the complete row with depth 13, base-four code 74800, original node 148899, kind 2, reserved field 0, 2861 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-4672-147487", "unmarked_context_11_4672_147487", "Unmarked parent at depth 11, code 4672",
                "The frontier Boolean is false at remaining fuel 10, original node 147487, the whole prefixCache at depth 11 and code 4672, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4674-148849", "unmarked_context_11_4674_148849", "Unmarked parent at depth 11, code 4674",
                "The frontier Boolean is false at remaining fuel 10, original node 148849, the whole prefixCache at depth 11 and code 4674, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-4672-147487", "node_context_11_4672_147487", "Original split at fuel 10 and node 147487",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 147002, 147126, 147302, 147486. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4674-148849", "node_context_11_4674_148849", "Original split at fuel 10 and node 148849",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 148391, 148513, 148664, 148848. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-4672-147487", "context_11_4672_147487", "Context at depth 11, code 4672, node 147487",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 4672 and original node 147487, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_18688_147002, context_12_18689_147126, context_12_18690_147302, context_12_18691_147486.", DescribeRole.Theorem),
            Node("context-13-74800-148899", "context_13_74800_148899", "Context at depth 13, code 74800, node 148899",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 74800 and original node 148899, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
