using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0020Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0020.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0020",
        H("Original frontier context coverage 0020"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00962", "selected_cut_00962", "Selected cut at depth 12, code 4196, node 1738",
                "At remaining fuel 9 and original index 1738, selection on the full partial prefix of depth 12 and code 4196 returns the complete row with depth 12, base-four code 4196, original node 1738, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01009", "selected_cut_01009", "Selected cut at depth 14, code 69667, node 40102",
                "At remaining fuel 7 and original index 40102, selection on the full partial prefix of depth 14 and code 69667 returns the complete row with depth 14, base-four code 69667, original node 40102, kind 2, reserved field 0, 1577 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-1048-37927", "unmarked_context_11_1048_37927", "Unmarked parent at depth 11, code 1048",
                "The frontier Boolean is false at remaining fuel 10, original node 37927, the whole prefixCache at depth 11 and code 1048, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4353-39985", "unmarked_context_12_4353_39985", "Unmarked parent at depth 12, code 4353",
                "The frontier Boolean is false at remaining fuel 9, original node 39985, the whole prefixCache at depth 12 and code 4353, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-1048-37927", "node_context_11_1048_37927", "Original split at fuel 10 and node 37927",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 1738, 37881, 37926. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4353-39985", "node_context_12_4353_39985", "Original split at fuel 9 and node 39985",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 39888, 39941, 39984, 414. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-1048-37927", "context_11_1048_37927", "Context at depth 11, code 1048, node 37927",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 1048 and original node 37927, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_4192_1738, context_12_4193_1738, context_12_4194_37881, context_12_4195_37926.", DescribeRole.Theorem),
            Node("context-14-69667-40102", "context_14_69667_40102", "Context at depth 14, code 69667, node 40102",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 69667 and original node 40102, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
