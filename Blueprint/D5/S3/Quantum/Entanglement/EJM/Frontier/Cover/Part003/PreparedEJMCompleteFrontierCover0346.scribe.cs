using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0346Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0346.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0346",
        H("Original frontier context coverage 0346"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16612", "selected_cut_16612", "Selected cut at depth 14, code 454756, node 422493",
                "At remaining fuel 7 and original index 422493, selection on the full partial prefix of depth 14 and code 454756 returns the complete row with depth 14, base-four code 454756, original node 422493, kind 2, reserved field 0, 1145 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16659", "selected_cut_16659", "Selected cut at depth 14, code 454839, node 423932",
                "At remaining fuel 7 and original index 423932, selection on the full partial prefix of depth 14 and code 454839 returns the complete row with depth 14, base-four code 454839, original node 423932, kind 2, reserved field 0, 977 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-113688-422466", "unmarked_context_13_113688_422466", "Unmarked parent at depth 13, code 113688",
                "The frontier Boolean is false at remaining fuel 8, original node 422466, the whole prefixCache at depth 13 and code 113688, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-113709-423933", "unmarked_context_13_113709_423933", "Unmarked parent at depth 13, code 113709",
                "The frontier Boolean is false at remaining fuel 8, original node 423933, the whole prefixCache at depth 13 and code 113709, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-113688-422466", "node_context_13_113688_422466", "Original split at fuel 8 and node 422466",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 422383, 422417, 422445, 422465. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-113709-423933", "node_context_13_113709_423933", "Original split at fuel 8 and node 423933",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 423865, 423895, 423918, 423932. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-113688-422466", "context_13_113688_422466", "Context at depth 13, code 113688, node 422466",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113688 and original node 422466, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_454752_422383, context_14_454753_422417, context_14_454754_422445, context_14_454755_422465.", DescribeRole.Theorem),
            Node("context-13-113709-423933", "context_13_113709_423933", "Context at depth 13, code 113709, node 423933",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113709 and original node 423933, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_454836_423865, context_14_454837_423895, context_14_454838_423918, context_14_454839_423932.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
