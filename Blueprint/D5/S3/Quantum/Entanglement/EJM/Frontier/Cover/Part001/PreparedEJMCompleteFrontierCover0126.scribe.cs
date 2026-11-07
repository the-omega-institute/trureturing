using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0126Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0126.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0126",
        H("Original frontier context coverage 0126"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06052", "selected_cut_06052", "Selected cut at depth 13, code 84202, node 183517",
                "At remaining fuel 8 and original index 183517, selection on the full partial prefix of depth 13 and code 84202 returns the complete row with depth 13, base-four code 84202, original node 183517, kind 2, reserved field 0, 2469 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06097", "selected_cut_06097", "Selected cut at depth 13, code 84247, node 184396",
                "At remaining fuel 8 and original index 184396, selection on the full partial prefix of depth 13 and code 84247 returns the complete row with depth 13, base-four code 84247, original node 184396, kind 2, reserved field 0, 921 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-84201-183477", "unmarked_context_13_84201_183477", "Unmarked parent at depth 13, code 84201",
                "The frontier Boolean is false at remaining fuel 8, original node 183477, the whole prefixCache at depth 13 and code 84201, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21061-184397", "unmarked_context_12_21061_184397", "Unmarked parent at depth 12, code 21061",
                "The frontier Boolean is false at remaining fuel 9, original node 184397, the whole prefixCache at depth 12 and code 21061, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-84201-183477", "node_context_13_84201_183477", "Original split at fuel 8 and node 183477",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 183429, 183450, 183465, 183476. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21061-184397", "node_context_12_21061_184397", "Original split at fuel 9 and node 184397",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 184365, 184389, 184396. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-84201-183477", "context_13_84201_183477", "Context at depth 13, code 84201, node 183477",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 84201 and original node 183477, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_336804_183429, context_14_336805_183450, context_14_336806_183465, context_14_336807_183476.", DescribeRole.Theorem),
            Node("context-12-21061-184397", "context_12_21061_184397", "Context at depth 12, code 21061, node 184397",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21061 and original node 184397, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_84244_3444, context_13_84245_184365, context_13_84246_184389, context_13_84247_184396.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
