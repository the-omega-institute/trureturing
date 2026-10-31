using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1020Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1020.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1020",
        H("Original frontier context coverage 1020"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48963", "selected_cut_48963", "Selected cut at depth 11, code 101217, node 1380866",
                "At remaining fuel 10 and original index 1380866, selection on the full partial prefix of depth 11 and code 101217 returns the complete row with depth 11, base-four code 101217, original node 1380866, kind 2, reserved field 0, 1773 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49011", "selected_cut_49011", "Selected cut at depth 11, code 101325, node 1382967",
                "At remaining fuel 10 and original index 1382967, selection on the full partial prefix of depth 11 and code 101325 returns the complete row with depth 11, base-four code 101325, original node 1382967, kind 2, reserved field 0, 3605 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25304-1380940", "unmarked_context_10_25304_1380940", "Unmarked parent at depth 10, code 25304",
                "The frontier Boolean is false at remaining fuel 11, original node 1380940, the whole prefixCache at depth 10 and code 25304, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-101324-1382876", "unmarked_context_11_101324_1382876", "Unmarked parent at depth 11, code 101324",
                "The frontier Boolean is false at remaining fuel 10, original node 1382876, the whole prefixCache at depth 11 and code 101324, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25304-1380940", "node_context_10_25304_1380940", "Original split at fuel 11 and node 1380940",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1380832, 1380866, 1380901, 1380939. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-101324-1382876", "node_context_11_101324_1382876", "Original split at fuel 10 and node 1382876",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1382758, 1382809, 1382875. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-101217-1380866", "context_11_101217_1380866", "Context at depth 11, code 101217, node 1380866",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 101217 and original node 1380866, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-101325-1382967", "context_11_101325_1382967", "Context at depth 11, code 101325, node 1382967",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 101325 and original node 1382967, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
