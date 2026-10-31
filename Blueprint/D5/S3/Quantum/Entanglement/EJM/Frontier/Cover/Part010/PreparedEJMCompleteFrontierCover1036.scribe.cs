using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1036Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1036.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1036",
        H("Original frontier context coverage 1036"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49732", "selected_cut_49732", "Selected cut at depth 11, code 102217, node 1409501",
                "At remaining fuel 10 and original index 1409501, selection on the full partial prefix of depth 11 and code 102217 returns the complete row with depth 11, base-four code 102217, original node 1409501, kind 2, reserved field 0, 3681 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49779", "selected_cut_49779", "Selected cut at depth 12, code 409119, node 1411229",
                "At remaining fuel 9 and original index 1411229, selection on the full partial prefix of depth 12 and code 409119 returns the complete row with depth 12, base-four code 409119, original node 1411229, kind 2, reserved field 0, 1141 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-102216-1409427", "unmarked_context_11_102216_1409427", "Unmarked parent at depth 11, code 102216",
                "The frontier Boolean is false at remaining fuel 10, original node 1409427, the whole prefixCache at depth 11 and code 102216, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-102279-1411230", "unmarked_context_11_102279_1411230", "Unmarked parent at depth 11, code 102279",
                "The frontier Boolean is false at remaining fuel 10, original node 1411230, the whole prefixCache at depth 11 and code 102279, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-102216-1409427", "node_context_11_102216_1409427", "Original split at fuel 10 and node 1409427",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1409323, 1409387, 1409426. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-102279-1411230", "node_context_11_102279_1411230", "Original split at fuel 10 and node 1411230",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1411119, 1411163, 1411229. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-102216-1409427", "context_11_102216_1409427", "Context at depth 11, code 102216, node 1409427",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 102216 and original node 1409427, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_408864_1108174, context_12_408865_1409323, context_12_408866_1409387, context_12_408867_1409426.", DescribeRole.Theorem),
            Node("context-11-102279-1411230", "context_11_102279_1411230", "Context at depth 11, code 102279, node 1411230",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 102279 and original node 1411230, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_409116_1108174, context_12_409117_1411119, context_12_409118_1411163, context_12_409119_1411229.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
