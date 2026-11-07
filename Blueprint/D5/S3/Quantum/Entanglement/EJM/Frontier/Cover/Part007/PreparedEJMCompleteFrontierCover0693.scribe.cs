using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0693Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0693.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0693",
        H("Original frontier context coverage 0693"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33268", "selected_cut_33268", "Selected cut at depth 13, code 440512, node 856762",
                "At remaining fuel 8 and original index 856762, selection on the full partial prefix of depth 13 and code 440512 returns the complete row with depth 13, base-four code 440512, original node 856762, kind 2, reserved field 0, 721 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33314", "selected_cut_33314", "Selected cut at depth 13, code 440579, node 857576",
                "At remaining fuel 8 and original index 857576, selection on the full partial prefix of depth 13 and code 440579 returns the complete row with depth 13, base-four code 440579, original node 857576, kind 2, reserved field 0, 665 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-6882-856748", "unmarked_context_10_6882_856748", "Unmarked parent at depth 10, code 6882",
                "The frontier Boolean is false at remaining fuel 11, original node 856748, the whole prefixCache at depth 10 and code 6882, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-110144-857577", "unmarked_context_12_110144_857577", "Unmarked parent at depth 12, code 110144",
                "The frontier Boolean is false at remaining fuel 9, original node 857577, the whole prefixCache at depth 12 and code 110144, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-6882-856748", "node_context_10_6882_856748", "Original split at fuel 11 and node 856748",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 855937, 856266, 856460, 856747. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-110144-857577", "node_context_12_110144_857577", "Original split at fuel 9 and node 857577",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 857539, 857571, 857576. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-6882-856748", "context_10_6882_856748", "Context at depth 10, code 6882, node 856748",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 6882 and original node 856748, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_27528_855937, context_11_27529_856266, context_11_27530_856460, context_11_27531_856747.", DescribeRole.Theorem),
            Node("context-12-110144-857577", "context_12_110144_857577", "Context at depth 12, code 110144, node 857577",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 110144 and original node 857577, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_440576_3444, context_13_440577_857539, context_13_440578_857571, context_13_440579_857576.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
