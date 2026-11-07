using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0371Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0371.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0371",
        H("Original frontier context coverage 0371"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17810", "selected_cut_17810", "Selected cut at depth 14, code 1134674, node 453746",
                "At remaining fuel 7 and original index 453746, selection on the full partial prefix of depth 14 and code 1134674 returns the complete row with depth 14, base-four code 1134674, original node 453746, kind 2, reserved field 0, 1913 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17857", "selected_cut_17857", "Selected cut at depth 12, code 70933, node 455939",
                "At remaining fuel 9 and original index 455939, selection on the full partial prefix of depth 12 and code 70933 returns the complete row with depth 12, base-four code 70933, original node 455939, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-283668-453747", "unmarked_context_13_283668_453747", "Unmarked parent at depth 13, code 283668",
                "The frontier Boolean is false at remaining fuel 8, original node 453747, the whole prefixCache at depth 13 and code 283668, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-17732-455736", "unmarked_context_11_17732_455736", "Unmarked parent at depth 11, code 17732",
                "The frontier Boolean is false at remaining fuel 10, original node 455736, the whole prefixCache at depth 11 and code 17732, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-283668-453747", "node_context_13_283668_453747", "Original split at fuel 8 and node 453747",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 453553, 453622, 453746, 291. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-17732-455736", "node_context_11_17732_455736", "Original split at fuel 10 and node 455736",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 455552, 455735, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-1134674-453746", "context_14_1134674_453746", "Context at depth 14, code 1134674, node 453746",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 1134674 and original node 453746, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-70933-455939", "context_12_70933_455939", "Context at depth 12, code 70933, node 455939",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 70933 and original node 455939, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
