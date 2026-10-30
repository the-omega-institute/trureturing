using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0640Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0640.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0640",
        H("Original frontier context coverage 0640"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30724", "selected_cut_30724", "Selected cut at depth 13, code 420040, node 780348",
                "At remaining fuel 8 and original index 780348, selection on the full partial prefix of depth 13 and code 420040 returns the complete row with depth 13, base-four code 420040, original node 780348, kind 2, reserved field 0, 741 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30771", "selected_cut_30771", "Selected cut at depth 12, code 105063, node 782047",
                "At remaining fuel 9 and original index 782047, selection on the full partial prefix of depth 12 and code 105063 returns the complete row with depth 12, base-four code 105063, original node 782047, kind 2, reserved field 0, 2061 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-105009-780335", "unmarked_context_12_105009_780335", "Unmarked parent at depth 12, code 105009",
                "The frontier Boolean is false at remaining fuel 9, original node 780335, the whole prefixCache at depth 12 and code 105009, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-26264-781898", "unmarked_context_11_26264_781898", "Unmarked parent at depth 11, code 26264",
                "The frontier Boolean is false at remaining fuel 10, original node 781898, the whole prefixCache at depth 11 and code 26264, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-105009-780335", "node_context_12_105009_780335", "Original split at fuel 9 and node 780335",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 780258, 780303, 780318, 780334. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-26264-781898", "node_context_11_26264_781898", "Original split at fuel 10 and node 781898",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 781788, 781828, 781859, 781897. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-105009-780335", "context_12_105009_780335", "Context at depth 12, code 105009, node 780335",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105009 and original node 780335, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_420036_780258, context_13_420037_780303, context_13_420038_780318, context_13_420039_780334.", DescribeRole.Theorem),
            Node("context-12-105063-782047", "context_12_105063_782047", "Context at depth 12, code 105063, node 782047",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105063 and original node 782047, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
