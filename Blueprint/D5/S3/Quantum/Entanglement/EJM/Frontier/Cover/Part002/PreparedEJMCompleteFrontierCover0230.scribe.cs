using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0230Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0230.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0230",
        H("Original frontier context coverage 0230"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11044", "selected_cut_11044", "Selected cut at depth 12, code 25408, node 296534",
                "At remaining fuel 9 and original index 296534, selection on the full partial prefix of depth 12 and code 25408 returns the complete row with depth 12, base-four code 25408, original node 296534, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11090", "selected_cut_11090", "Selected cut at depth 13, code 101687, node 297511",
                "At remaining fuel 8 and original index 297511, selection on the full partial prefix of depth 13 and code 101687 returns the complete row with depth 13, base-four code 101687, original node 297511, kind 2, reserved field 0, 857 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6351-296531", "unmarked_context_11_6351_296531", "Unmarked parent at depth 11, code 6351",
                "The frontier Boolean is false at remaining fuel 10, original node 296531, the whole prefixCache at depth 11 and code 6351, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25421-297512", "unmarked_context_12_25421_297512", "Unmarked parent at depth 12, code 25421",
                "The frontier Boolean is false at remaining fuel 9, original node 297512, the whole prefixCache at depth 12 and code 25421, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6351-296531", "node_context_11_6351_296531", "Original split at fuel 10 and node 296531",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 296410, 296473, 296529, 296530. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25421-297512", "node_context_12_25421_297512", "Original split at fuel 9 and node 297512",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 297480, 297502, 297511. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-6351-296531", "context_11_6351_296531", "Context at depth 11, code 6351, node 296531",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6351 and original node 296531, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_25404_296410, context_12_25405_296473, context_12_25406_296529, context_12_25407_296530.", DescribeRole.Theorem),
            Node("context-12-25421-297512", "context_12_25421_297512", "Context at depth 12, code 25421, node 297512",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25421 and original node 297512, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_101684_3444, context_13_101685_297480, context_13_101686_297502, context_13_101687_297511.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
