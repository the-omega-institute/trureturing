using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0170Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0170.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0170",
        H("Original frontier context coverage 0170"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08163", "selected_cut_08163", "Selected cut at depth 13, code 91392, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 91392 returns the complete row with depth 13, base-four code 91392, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08210", "selected_cut_08210", "Selected cut at depth 13, code 91442, node 231800",
                "At remaining fuel 8 and original index 231800, selection on the full partial prefix of depth 13 and code 91442 returns the complete row with depth 13, base-four code 91442, original node 231800, kind 2, reserved field 0, 1681 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1427-231106", "unmarked_context_10_1427_231106", "Unmarked parent at depth 10, code 1427",
                "The frontier Boolean is false at remaining fuel 11, original node 231106, the whole prefixCache at depth 10 and code 1427, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5714-231758", "unmarked_context_11_5714_231758", "Unmarked parent at depth 11, code 5714",
                "The frontier Boolean is false at remaining fuel 10, original node 231758, the whole prefixCache at depth 11 and code 5714, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1427-231106", "node_context_10_1427_231106", "Original split at fuel 11 and node 231106",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 230356, 230609, 230879, 231105. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5714-231758", "node_context_11_5714_231758", "Original split at fuel 10 and node 231758",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 231584, 231641, 231697, 231757. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-1427-231106", "context_10_1427_231106", "Context at depth 10, code 1427, node 231106",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1427 and original node 231106, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_5708_230356, context_11_5709_230609, context_11_5710_230879, context_11_5711_231105.", DescribeRole.Theorem),
            Node("context-13-91442-231800", "context_13_91442_231800", "Context at depth 13, code 91442, node 231800",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 91442 and original node 231800, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
