using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0708Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0708.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0708",
        H("Original frontier context coverage 0708"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33987", "selected_cut_33987", "Selected cut at depth 11, code 28224, node 434745",
                "At remaining fuel 10 and original index 434745, selection on the full partial prefix of depth 11 and code 28224 returns the complete row with depth 11, base-four code 28224, original node 434745, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34035", "selected_cut_34035", "Selected cut at depth 13, code 451683, node 879247",
                "At remaining fuel 8 and original index 879247, selection on the full partial prefix of depth 13 and code 451683 returns the complete row with depth 13, base-four code 451683, original node 879247, kind 2, reserved field 0, 673 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-8-440-878224", "unmarked_context_8_440_878224", "Unmarked parent at depth 8, code 440",
                "The frontier Boolean is false at remaining fuel 13, original node 878224, the whole prefixCache at depth 8 and code 440, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-28229-879186", "unmarked_context_11_28229_879186", "Unmarked parent at depth 11, code 28229",
                "The frontier Boolean is false at remaining fuel 10, original node 879186, the whole prefixCache at depth 11 and code 28229, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-8-440-878224", "node_context_8_440_878224", "Original split at fuel 13 and node 878224",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 875477, 877646, 878137, 878223. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-28229-879186", "node_context_11_28229_879186", "Original split at fuel 10 and node 879186",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 879037, 439069, 879112, 879185. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-8-440-878224", "context_8_440_878224", "Context at depth 8, code 440, node 878224",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 440 and original node 878224, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_9_1760_875477, context_9_1761_877646, context_9_1762_878137, context_9_1763_878223.", DescribeRole.Theorem),
            Node("context-13-451683-879247", "context_13_451683_879247", "Context at depth 13, code 451683, node 879247",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 451683 and original node 879247, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
