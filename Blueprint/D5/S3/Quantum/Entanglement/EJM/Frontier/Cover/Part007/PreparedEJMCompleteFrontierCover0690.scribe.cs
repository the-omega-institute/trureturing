using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0690Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0690.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0690",
        H("Original frontier context coverage 0690"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33124", "selected_cut_33124", "Selected cut at depth 11, code 27511, node 853558",
                "At remaining fuel 10 and original index 853558, selection on the full partial prefix of depth 11 and code 27511 returns the complete row with depth 11, base-four code 27511, original node 853558, kind 2, reserved field 0, 1685 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33171", "selected_cut_33171", "Selected cut at depth 13, code 440409, node 854806",
                "At remaining fuel 8 and original index 854806, selection on the full partial prefix of depth 13 and code 440409 returns the complete row with depth 13, base-four code 440409, original node 854806, kind 2, reserved field 0, 2293 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-6877-853559", "unmarked_context_10_6877_853559", "Unmarked parent at depth 10, code 6877",
                "The frontier Boolean is false at remaining fuel 11, original node 853559, the whole prefixCache at depth 10 and code 6877, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-110101-854759", "unmarked_context_12_110101_854759", "Unmarked parent at depth 12, code 110101",
                "The frontier Boolean is false at remaining fuel 9, original node 854759, the whole prefixCache at depth 12 and code 110101, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-6877-853559", "node_context_10_6877_853559", "Original split at fuel 11 and node 853559",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 853504, 853519, 853539, 853558. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-110101-854759", "node_context_12_110101_854759", "Original split at fuel 9 and node 854759",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 854688, 854714, 854749, 854758. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-27511-853558", "context_11_27511_853558", "Context at depth 11, code 27511, node 853558",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27511 and original node 853558, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-440409-854806", "context_13_440409_854806", "Context at depth 13, code 440409, node 854806",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 440409 and original node 854806, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
