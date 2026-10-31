using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0935Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0935.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0935",
        H("Original frontier context coverage 0935"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44883", "selected_cut_44883", "Selected cut at depth 12, code 355350, node 1237895",
                "At remaining fuel 9 and original index 1237895, selection on the full partial prefix of depth 12 and code 355350 returns the complete row with depth 12, base-four code 355350, original node 1237895, kind 2, reserved field 0, 3141 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44930", "selected_cut_44930", "Selected cut at depth 12, code 355403, node 1239830",
                "At remaining fuel 9 and original index 1239830, selection on the full partial prefix of depth 12 and code 355403 returns the complete row with depth 12, base-four code 355403, original node 1239830, kind 2, reserved field 0, 1877 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88837-1237963", "unmarked_context_11_88837_1237963", "Unmarked parent at depth 11, code 88837",
                "The frontier Boolean is false at remaining fuel 10, original node 1237963, the whole prefixCache at depth 11 and code 88837, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88850-1239831", "unmarked_context_11_88850_1239831", "Unmarked parent at depth 11, code 88850",
                "The frontier Boolean is false at remaining fuel 10, original node 1239831, the whole prefixCache at depth 11 and code 88850, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88837-1237963", "node_context_11_88837_1237963", "Original split at fuel 10 and node 1237963",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 1172003, 1237895, 1237962. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88850-1239831", "node_context_11_88850_1239831", "Original split at fuel 10 and node 1239831",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1239747, 896706, 1239785, 1239830. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-355350-1237895", "context_12_355350_1237895", "Context at depth 12, code 355350, node 1237895",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 355350 and original node 1237895, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-88850-1239831", "context_11_88850_1239831", "Context at depth 11, code 88850, node 1239831",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88850 and original node 1239831, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_355400_1239747, context_12_355401_896706, context_12_355402_1239785, context_12_355403_1239830.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
