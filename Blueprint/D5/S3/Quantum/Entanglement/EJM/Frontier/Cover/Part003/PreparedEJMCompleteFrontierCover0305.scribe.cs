using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0305Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0305.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0305",
        H("Original frontier context coverage 0305"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14644", "selected_cut_14644", "Selected cut at depth 13, code 109594, node 377383",
                "At remaining fuel 8 and original index 377383, selection on the full partial prefix of depth 13 and code 109594 returns the complete row with depth 13, base-four code 109594, original node 377383, kind 2, reserved field 0, 2613 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14691", "selected_cut_14691", "Selected cut at depth 14, code 438516, node 378977",
                "At remaining fuel 7 and original index 378977, selection on the full partial prefix of depth 14 and code 438516 returns the complete row with depth 14, base-four code 438516, original node 378977, kind 2, reserved field 0, 1889 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-109593-377330", "unmarked_context_13_109593_377330", "Unmarked parent at depth 13, code 109593",
                "The frontier Boolean is false at remaining fuel 8, original node 377330, the whole prefixCache at depth 13 and code 109593, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-109628-378930", "unmarked_context_13_109628_378930", "Unmarked parent at depth 13, code 109628",
                "The frontier Boolean is false at remaining fuel 8, original node 378930, the whole prefixCache at depth 13 and code 109628, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-109593-377330", "node_context_13_109593_377330", "Original split at fuel 8 and node 377330",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 377276, 377292, 377312, 377329. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-109628-378930", "node_context_13_109628_378930", "Original split at fuel 8 and node 378930",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 378840, 378873, 378901, 378929. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-109593-377330", "context_13_109593_377330", "Context at depth 13, code 109593, node 377330",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109593 and original node 377330, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_438372_377276, context_14_438373_377292, context_14_438374_377312, context_14_438375_377329.", DescribeRole.Theorem),
            Node("context-14-438516-378977", "context_14_438516_378977", "Context at depth 14, code 438516, node 378977",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 438516 and original node 378977, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
