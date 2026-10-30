using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0995Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0995.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0995",
        H("Original frontier context coverage 0995"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47763", "selected_cut_47763", "Selected cut at depth 11, code 93573, node 892405",
                "At remaining fuel 10 and original index 892405, selection on the full partial prefix of depth 11 and code 93573 returns the complete row with depth 11, base-four code 93573, original node 892405, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47810", "selected_cut_47810", "Selected cut at depth 12, code 374351, node 1339049",
                "At remaining fuel 9 and original index 1339049, selection on the full partial prefix of depth 12 and code 374351 returns the complete row with depth 12, base-four code 374351, original node 1339049, kind 2, reserved field 0, 1849 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93574-1337436", "unmarked_context_11_93574_1337436", "Unmarked parent at depth 11, code 93574",
                "The frontier Boolean is false at remaining fuel 10, original node 1337436, the whole prefixCache at depth 11 and code 93574, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23396-1339051", "unmarked_context_10_23396_1339051", "Unmarked parent at depth 10, code 23396",
                "The frontier Boolean is false at remaining fuel 11, original node 1339051, the whole prefixCache at depth 10 and code 23396, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93574-1337436", "node_context_11_93574_1337436", "Original split at fuel 10 and node 1337436",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994572, 1337383, 893903, 1337435. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23396-1339051", "node_context_10_23396_1339051", "Original split at fuel 11 and node 1339051",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1283168, 1338810, 1338902, 1339050. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-93573-892405", "context_11_93573_892405", "Context at depth 11, code 93573, node 892405",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93573 and original node 892405, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-23396-1339051", "context_10_23396_1339051", "Context at depth 10, code 23396, node 1339051",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23396 and original node 1339051, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_93584_1283168, context_11_93585_1338810, context_11_93586_1338902, context_11_93587_1339050.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
