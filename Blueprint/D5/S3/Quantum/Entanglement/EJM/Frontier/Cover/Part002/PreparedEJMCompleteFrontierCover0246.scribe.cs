using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0246Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0246.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0246",
        H("Original frontier context coverage 0246"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11810", "selected_cut_11810", "Selected cut at depth 13, code 103496, node 316047",
                "At remaining fuel 8 and original index 316047, selection on the full partial prefix of depth 13 and code 103496 returns the complete row with depth 13, base-four code 103496, original node 316047, kind 2, reserved field 0, 2129 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11858", "selected_cut_11858", "Selected cut at depth 13, code 103547, node 317071",
                "At remaining fuel 8 and original index 317071, selection on the full partial prefix of depth 13 and code 103547 returns the complete row with depth 13, base-four code 103547, original node 317071, kind 2, reserved field 0, 821 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25874-316100", "unmarked_context_12_25874_316100", "Unmarked parent at depth 12, code 25874",
                "The frontier Boolean is false at remaining fuel 9, original node 316100, the whole prefixCache at depth 12 and code 25874, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25886-317072", "unmarked_context_12_25886_317072", "Unmarked parent at depth 12, code 25886",
                "The frontier Boolean is false at remaining fuel 9, original node 317072, the whole prefixCache at depth 12 and code 25886, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25874-316100", "node_context_12_25874_316100", "Original split at fuel 9 and node 316100",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 316047, 316072, 316091, 316099. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25886-317072", "node_context_12_25886_317072", "Original split at fuel 9 and node 317072",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 317019, 317043, 317064, 317071. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-103496-316047", "context_13_103496_316047", "Context at depth 13, code 103496, node 316047",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 103496 and original node 316047, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25886-317072", "context_12_25886_317072", "Context at depth 12, code 25886, node 317072",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25886 and original node 317072, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_103544_317019, context_13_103545_317043, context_13_103546_317064, context_13_103547_317071.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
