using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0348Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0348.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0348",
        H("Original frontier context coverage 0348"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16708", "selected_cut_16708", "Selected cut at depth 13, code 113752, node 425607",
                "At remaining fuel 8 and original index 425607, selection on the full partial prefix of depth 13 and code 113752 returns the complete row with depth 13, base-four code 113752, original node 425607, kind 2, reserved field 0, 2781 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16754", "selected_cut_16754", "Selected cut at depth 13, code 113795, node 426789",
                "At remaining fuel 8 and original index 426789, selection on the full partial prefix of depth 13 and code 113795 returns the complete row with depth 13, base-four code 113795, original node 426789, kind 2, reserved field 0, 669 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28437-425565", "unmarked_context_12_28437_425565", "Unmarked parent at depth 12, code 28437",
                "The frontier Boolean is false at remaining fuel 9, original node 425565, the whole prefixCache at depth 12 and code 28437, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-28448-426790", "unmarked_context_12_28448_426790", "Unmarked parent at depth 12, code 28448",
                "The frontier Boolean is false at remaining fuel 9, original node 426790, the whole prefixCache at depth 12 and code 28448, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28437-425565", "node_context_12_28437_425565", "Original split at fuel 9 and node 425565",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 425493, 425532, 425556, 425564. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-28448-426790", "node_context_12_28448_426790", "Original split at fuel 9 and node 426790",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 426736, 426765, 426784, 426789. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-28437-425565", "context_12_28437_425565", "Context at depth 12, code 28437, node 425565",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28437 and original node 425565, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_113748_425493, context_13_113749_425532, context_13_113750_425556, context_13_113751_425564.", DescribeRole.Theorem),
            Node("context-12-28448-426790", "context_12_28448_426790", "Context at depth 12, code 28448, node 426790",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28448 and original node 426790, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_113792_426736, context_13_113793_426765, context_13_113794_426784, context_13_113795_426789.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
