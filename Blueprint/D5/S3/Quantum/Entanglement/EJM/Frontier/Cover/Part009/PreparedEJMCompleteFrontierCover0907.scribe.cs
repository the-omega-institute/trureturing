using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0907Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0907.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0907",
        H("Original frontier context coverage 0907"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43540", "selected_cut_43540", "Selected cut at depth 11, code 87712, node 1192655",
                "At remaining fuel 10 and original index 1192655, selection on the full partial prefix of depth 11 and code 87712 returns the complete row with depth 11, base-four code 87712, original node 1192655, kind 2, reserved field 0, 2209 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43587", "selected_cut_43587", "Selected cut at depth 12, code 351006, node 1194644",
                "At remaining fuel 9 and original index 1194644, selection on the full partial prefix of depth 12 and code 351006 returns the complete row with depth 12, base-four code 351006, original node 1194644, kind 2, reserved field 0, 3221 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-21927-1192615", "unmarked_context_10_21927_1192615", "Unmarked parent at depth 10, code 21927",
                "The frontier Boolean is false at remaining fuel 11, original node 1192615, the whole prefixCache at depth 10 and code 21927, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-87750-1194487", "unmarked_context_11_87750_1194487", "Unmarked parent at depth 11, code 87750",
                "The frontier Boolean is false at remaining fuel 10, original node 1194487, the whole prefixCache at depth 11 and code 87750, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-21927-1192615", "node_context_10_21927_1192615", "Original split at fuel 11 and node 1192615",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1192462, 1192511, 1192559, 1192614. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-87750-1194487", "node_context_11_87750_1194487", "Original split at fuel 10 and node 1194487",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1194313, 1194371, 1194422, 1194486. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-21927-1192615", "context_10_21927_1192615", "Context at depth 10, code 21927, node 1192615",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21927 and original node 1192615, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_87708_1192462, context_11_87709_1192511, context_11_87710_1192559, context_11_87711_1192614.", DescribeRole.Theorem),
            Node("context-12-351006-1194644", "context_12_351006_1194644", "Context at depth 12, code 351006, node 1194644",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 351006 and original node 1194644, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
