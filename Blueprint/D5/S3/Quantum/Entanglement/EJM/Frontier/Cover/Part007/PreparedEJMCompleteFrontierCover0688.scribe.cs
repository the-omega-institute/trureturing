using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0688Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0688.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0688",
        H("Original frontier context coverage 0688"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33027", "selected_cut_33027", "Selected cut at depth 12, code 109905, node 850237",
                "At remaining fuel 9 and original index 850237, selection on the full partial prefix of depth 12 and code 109905 returns the complete row with depth 12, base-four code 109905, original node 850237, kind 2, reserved field 0, 3605 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33074", "selected_cut_33074", "Selected cut at depth 12, code 109952, node 852202",
                "At remaining fuel 9 and original index 852202, selection on the full partial prefix of depth 12 and code 109952 returns the complete row with depth 12, base-four code 109952, original node 852202, kind 2, reserved field 0, 2273 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-109907-850374", "unmarked_context_12_109907_850374", "Unmarked parent at depth 12, code 109907",
                "The frontier Boolean is false at remaining fuel 9, original node 850374, the whole prefixCache at depth 12 and code 109907, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1717-852170", "unmarked_context_9_1717_852170", "Unmarked parent at depth 9, code 1717",
                "The frontier Boolean is false at remaining fuel 12, original node 852170, the whole prefixCache at depth 9 and code 1717, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-109907-850374", "node_context_12_109907_850374", "Original split at fuel 9 and node 850374",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 850323, 850364, 850373. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1717-852170", "node_context_9_1717_852170", "Original split at fuel 12 and node 852170",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 850138, 850908, 851677, 852169. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-109905-850237", "context_12_109905_850237", "Context at depth 12, code 109905, node 850237",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109905 and original node 850237, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-109952-852202", "context_12_109952_852202", "Context at depth 12, code 109952, node 852202",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109952 and original node 852202, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
