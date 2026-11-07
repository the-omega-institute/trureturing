using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0229Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0229.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0229",
        H("Original frontier context coverage 0229"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10995", "selected_cut_10995", "Selected cut at depth 13, code 101577, node 295788",
                "At remaining fuel 8 and original index 295788, selection on the full partial prefix of depth 13 and code 101577 returns the complete row with depth 13, base-four code 101577, original node 295788, kind 2, reserved field 0, 1933 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11043", "selected_cut_11043", "Selected cut at depth 12, code 25407, node 296530",
                "At remaining fuel 9 and original index 296530, selection on the full partial prefix of depth 12 and code 25407 returns the complete row with depth 12, base-four code 25407, original node 296530, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25394-295812", "unmarked_context_12_25394_295812", "Unmarked parent at depth 12, code 25394",
                "The frontier Boolean is false at remaining fuel 9, original node 295812, the whole prefixCache at depth 12 and code 25394, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25406-296529", "unmarked_context_12_25406_296529", "Unmarked parent at depth 12, code 25406",
                "The frontier Boolean is false at remaining fuel 9, original node 296529, the whole prefixCache at depth 12 and code 25406, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25394-295812", "node_context_12_25394_295812", "Original split at fuel 9 and node 295812",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 295764, 295788, 295804, 295811. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25406-296529", "node_context_12_25406_296529", "Original split at fuel 9 and node 296529",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 296477, 296500, 296520, 296528. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-101577-295788", "context_13_101577_295788", "Context at depth 13, code 101577, node 295788",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 101577 and original node 295788, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25407-296530", "context_12_25407_296530", "Context at depth 12, code 25407, node 296530",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25407 and original node 296530, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
