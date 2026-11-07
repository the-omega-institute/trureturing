using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1072Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1072.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1072",
        H("Original frontier context coverage 1072"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51459", "selected_cut_51459", "Selected cut at depth 11, code 281223, node 1484335",
                "At remaining fuel 10 and original index 1484335, selection on the full partial prefix of depth 11 and code 281223 returns the complete row with depth 11, base-four code 281223, original node 1484335, kind 2, reserved field 0, 2357 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51506", "selected_cut_51506", "Selected cut at depth 11, code 281540, node 1486307",
                "At remaining fuel 10 and original index 1486307, selection on the full partial prefix of depth 11 and code 281540 returns the complete row with depth 11, base-four code 281540, original node 1486307, kind 2, reserved field 0, 3421 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-70305-1484336", "unmarked_context_10_70305_1484336", "Unmarked parent at depth 10, code 70305",
                "The frontier Boolean is false at remaining fuel 11, original node 1484336, the whole prefixCache at depth 10 and code 70305, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-7-1098-1486187", "unmarked_context_7_1098_1486187", "Unmarked parent at depth 7, code 1098",
                "The frontier Boolean is false at remaining fuel 14, original node 1486187, the whole prefixCache at depth 7 and code 1098, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-70305-1484336", "node_context_10_70305_1484336", "Original split at fuel 11 and node 1484336",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1483983, 1468419, 1484175, 1484335. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-7-1098-1486187", "node_context_7_1098_1486187", "Original split at fuel 14 and node 1486187",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 14300, 14300, 1485073, 1486186. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-281223-1484335", "context_11_281223_1484335", "Context at depth 11, code 281223, node 1484335",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 281223 and original node 1484335, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-281540-1486307", "context_11_281540_1486307", "Context at depth 11, code 281540, node 1486307",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 281540 and original node 1486307, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
