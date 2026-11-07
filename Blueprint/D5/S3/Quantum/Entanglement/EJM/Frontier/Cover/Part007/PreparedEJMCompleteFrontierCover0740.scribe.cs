using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0740Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0740.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0740",
        H("Original frontier context coverage 0740"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35523", "selected_cut_35523", "Selected cut at depth 12, code 286863, node 934144",
                "At remaining fuel 9 and original index 934144, selection on the full partial prefix of depth 12 and code 286863 returns the complete row with depth 12, base-four code 286863, original node 934144, kind 2, reserved field 0, 1465 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35570", "selected_cut_35570", "Selected cut at depth 12, code 287003, node 935904",
                "At remaining fuel 9 and original index 935904, selection on the full partial prefix of depth 12 and code 287003 returns the complete row with depth 12, base-four code 287003, original node 935904, kind 2, reserved field 0, 3573 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71715-934145", "unmarked_context_11_71715_934145", "Unmarked parent at depth 11, code 71715",
                "The frontier Boolean is false at remaining fuel 10, original node 934145, the whole prefixCache at depth 11 and code 71715, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71749-935683", "unmarked_context_11_71749_935683", "Unmarked parent at depth 11, code 71749",
                "The frontier Boolean is false at remaining fuel 10, original node 935683, the whole prefixCache at depth 11 and code 71749, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71715-934145", "node_context_11_71715_934145", "Original split at fuel 10 and node 934145",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 934071, 934093, 934118, 934144. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71749-935683", "node_context_11_71749_935683", "Original split at fuel 10 and node 935683",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 935598, 124308, 935638, 935682. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-286863-934144", "context_12_286863_934144", "Context at depth 12, code 286863, node 934144",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 286863 and original node 934144, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-287003-935904", "context_12_287003_935904", "Context at depth 12, code 287003, node 935904",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287003 and original node 935904, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
