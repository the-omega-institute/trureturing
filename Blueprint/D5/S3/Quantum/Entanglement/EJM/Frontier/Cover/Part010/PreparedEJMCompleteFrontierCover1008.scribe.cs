using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1008Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1008.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1008",
        H("Original frontier context coverage 1008"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48388", "selected_cut_48388", "Selected cut at depth 12, code 376102, node 1357642",
                "At remaining fuel 9 and original index 1357642, selection on the full partial prefix of depth 12 and code 376102 returns the complete row with depth 12, base-four code 376102, original node 1357642, kind 2, reserved field 0, 2533 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48435", "selected_cut_48435", "Selected cut at depth 10, code 23514, node 1358976",
                "At remaining fuel 11 and original index 1358976, selection on the full partial prefix of depth 10 and code 23514 returns the complete row with depth 10, base-four code 23514, original node 1358976, kind 2, reserved field 0, 2197 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-94025-1357685", "unmarked_context_11_94025_1357685", "Unmarked parent at depth 11, code 94025",
                "The frontier Boolean is false at remaining fuel 10, original node 1357685, the whole prefixCache at depth 11 and code 94025, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23513-1358936", "unmarked_context_10_23513_1358936", "Unmarked parent at depth 10, code 23513",
                "The frontier Boolean is false at remaining fuel 11, original node 1358936, the whole prefixCache at depth 10 and code 23513, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-94025-1357685", "node_context_11_94025_1357685", "Original split at fuel 10 and node 1357685",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 891951, 1357642, 1357684. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23513-1358936", "node_context_10_23513_1358936", "Original split at fuel 11 and node 1358936",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1358876, 1358888, 1358919, 1358935. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-376102-1357642", "context_12_376102_1357642", "Context at depth 12, code 376102, node 1357642",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 376102 and original node 1357642, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-23514-1358976", "context_10_23514_1358976", "Context at depth 10, code 23514, node 1358976",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23514 and original node 1358976, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
