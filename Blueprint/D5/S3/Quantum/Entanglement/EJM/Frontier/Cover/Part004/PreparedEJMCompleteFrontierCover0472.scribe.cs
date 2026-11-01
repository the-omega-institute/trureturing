using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0472Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0472.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0472",
        H("Original frontier context coverage 0472"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22659", "selected_cut_22659", "Selected cut at depth 12, code 75828, node 475533",
                "At remaining fuel 9 and original index 475533, selection on the full partial prefix of depth 12 and code 75828 returns the complete row with depth 12, base-four code 75828, original node 475533, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22705", "selected_cut_22705", "Selected cut at depth 12, code 75847, node 576497",
                "At remaining fuel 9 and original index 576497, selection on the full partial prefix of depth 12 and code 75847 returns the complete row with depth 12, base-four code 75847, original node 576497, kind 2, reserved field 0, 3617 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18956-575645", "unmarked_context_11_18956_575645", "Unmarked parent at depth 11, code 18956",
                "The frontier Boolean is false at remaining fuel 10, original node 575645, the whole prefixCache at depth 11 and code 18956, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18961-576498", "unmarked_context_11_18961_576498", "Unmarked parent at depth 11, code 18961",
                "The frontier Boolean is false at remaining fuel 10, original node 576498, the whole prefixCache at depth 11 and code 18961, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18956-575645", "node_context_11_18956_575645", "Original split at fuel 10 and node 575645",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 445562, 575525, 575580, 575644. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18961-576498", "node_context_11_18961_576498", "Original split at fuel 10 and node 576498",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 576365, 576407, 576447, 576497. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-18956-575645", "context_11_18956_575645", "Context at depth 11, code 18956, node 575645",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18956 and original node 575645, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_75824_445562, context_12_75825_575525, context_12_75826_575580, context_12_75827_575644.", DescribeRole.Theorem),
            Node("context-11-18961-576498", "context_11_18961_576498", "Context at depth 11, code 18961, node 576498",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18961 and original node 576498, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_75844_576365, context_12_75845_576407, context_12_75846_576447, context_12_75847_576497.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
