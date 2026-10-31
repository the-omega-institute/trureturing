using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1074Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1074.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1074",
        H("Original frontier context coverage 1074"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51554", "selected_cut_51554", "Selected cut at depth 10, code 70697, node 1488516",
                "At remaining fuel 11 and original index 1488516, selection on the full partial prefix of depth 10 and code 70697 returns the complete row with depth 10, base-four code 70697, original node 1488516, kind 2, reserved field 0, 2985 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51602", "selected_cut_51602", "Selected cut at depth 10, code 70763, node 1490257",
                "At remaining fuel 11 and original index 1490257, selection on the full partial prefix of depth 10 and code 70763 returns the complete row with depth 10, base-four code 70763, original node 1490257, kind 2, reserved field 0, 2293 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-17674-1488576", "unmarked_context_9_17674_1488576", "Unmarked parent at depth 9, code 17674",
                "The frontier Boolean is false at remaining fuel 12, original node 1488576, the whole prefixCache at depth 9 and code 17674, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-17689-1490103", "unmarked_context_9_17689_1490103", "Unmarked parent at depth 9, code 17689",
                "The frontier Boolean is false at remaining fuel 12, original node 1490103, the whole prefixCache at depth 9 and code 17689, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-17674-1488576", "node_context_9_17674_1488576", "Original split at fuel 12 and node 1488576",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1488444, 1488516, 1469103, 1488575. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-17689-1490103", "node_context_9_17689_1490103", "Original split at fuel 12 and node 1490103",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1489900, 1468874, 1490006, 1490102. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-70697-1488516", "context_10_70697_1488516", "Context at depth 10, code 70697, node 1488516",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 70697 and original node 1488516, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-70763-1490257", "context_10_70763_1490257", "Context at depth 10, code 70763, node 1490257",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 70763 and original node 1490257, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
