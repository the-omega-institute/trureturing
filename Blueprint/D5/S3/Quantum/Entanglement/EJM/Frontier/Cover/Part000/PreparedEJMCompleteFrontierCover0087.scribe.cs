using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0087Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0087.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0087",
        H("Original frontier context coverage 0087"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04179", "selected_cut_04179", "Selected cut at depth 12, code 17970, node 132182",
                "At remaining fuel 9 and original index 132182, selection on the full partial prefix of depth 12 and code 17970 returns the complete row with depth 12, base-four code 17970, original node 132182, kind 2, reserved field 0, 4053 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04225", "selected_cut_04225", "Selected cut at depth 12, code 18004, node 895",
                "At remaining fuel 9 and original index 895, selection on the full partial prefix of depth 12 and code 18004 returns the complete row with depth 12, base-four code 18004, original node 895, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-17969-132093", "unmarked_context_12_17969_132093", "Unmarked parent at depth 12, code 17969",
                "The frontier Boolean is false at remaining fuel 9, original node 132093, the whole prefixCache at depth 12 and code 17969, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4500-133577", "unmarked_context_11_4500_133577", "Unmarked parent at depth 11, code 4500",
                "The frontier Boolean is false at remaining fuel 10, original node 133577, the whole prefixCache at depth 11 and code 4500, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-17969-132093", "node_context_12_17969_132093", "Original split at fuel 9 and node 132093",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 132007, 132068, 132083, 132092. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4500-133577", "node_context_11_4500_133577", "Original split at fuel 10 and node 133577",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 133339, 133439, 133510, 133576. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-17969-132093", "context_12_17969_132093", "Context at depth 12, code 17969, node 132093",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 17969 and original node 132093, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_71876_132007, context_13_71877_132068, context_13_71878_132083, context_13_71879_132092.", DescribeRole.Theorem),
            Node("context-12-18004-895", "context_12_18004_895", "Context at depth 12, code 18004, node 895",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18004 and original node 895, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
