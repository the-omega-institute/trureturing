using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1011Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1011.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1011",
        H("Original frontier context coverage 1011"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48532", "selected_cut_48532", "Selected cut at depth 12, code 376588, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 376588 returns the complete row with depth 12, base-four code 376588, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48579", "selected_cut_48579", "Selected cut at depth 12, code 376647, node 1363639",
                "At remaining fuel 9 and original index 1363639, selection on the full partial prefix of depth 12 and code 376647 returns the complete row with depth 12, base-four code 376647, original node 1363639, kind 2, reserved field 0, 1913 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-94147-1362191", "unmarked_context_11_94147_1362191", "Unmarked parent at depth 11, code 94147",
                "The frontier Boolean is false at remaining fuel 10, original node 1362191, the whole prefixCache at depth 11 and code 94147, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-94161-1363640", "unmarked_context_11_94161_1363640", "Unmarked parent at depth 11, code 94161",
                "The frontier Boolean is false at remaining fuel 10, original node 1363640, the whole prefixCache at depth 11 and code 94161, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-94147-1362191", "node_context_11_94147_1362191", "Original split at fuel 10 and node 1362191",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1362132, 1362190, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-94161-1363640", "node_context_11_94161_1363640", "Original split at fuel 10 and node 1363640",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1363567, 1257136, 1363606, 1363639. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-376588-448748", "context_12_376588_448748", "Context at depth 12, code 376588, node 448748",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 376588 and original node 448748, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-94161-1363640", "context_11_94161_1363640", "Context at depth 11, code 94161, node 1363640",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 94161 and original node 1363640, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_376644_1363567, context_12_376645_1257136, context_12_376646_1363606, context_12_376647_1363639.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
