using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0471Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0471.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0471",
        H("Original frontier context coverage 0471"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22610", "selected_cut_22610", "Selected cut at depth 12, code 75812, node 450498",
                "At remaining fuel 9 and original index 450498, selection on the full partial prefix of depth 12 and code 75812 returns the complete row with depth 12, base-four code 75812, original node 450498, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22658", "selected_cut_22658", "Selected cut at depth 13, code 303311, node 575643",
                "At remaining fuel 8 and original index 575643, selection on the full partial prefix of depth 13 and code 303311 returns the complete row with depth 13, base-four code 303311, original node 575643, kind 2, reserved field 0, 637 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75813-574985", "unmarked_context_12_75813_574985", "Unmarked parent at depth 12, code 75813",
                "The frontier Boolean is false at remaining fuel 9, original node 574985, the whole prefixCache at depth 12 and code 75813, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75827-575644", "unmarked_context_12_75827_575644", "Unmarked parent at depth 12, code 75827",
                "The frontier Boolean is false at remaining fuel 9, original node 575644, the whole prefixCache at depth 12 and code 75827, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75813-574985", "node_context_12_75813_574985", "Original split at fuel 9 and node 574985",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 574944, 574963, 574979, 574984. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75827-575644", "node_context_12_75827_575644", "Original split at fuel 9 and node 575644",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 575589, 575619, 575637, 575643. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75812-450498", "context_12_75812_450498", "Context at depth 12, code 75812, node 450498",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75812 and original node 450498, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-75827-575644", "context_12_75827_575644", "Context at depth 12, code 75827, node 575644",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75827 and original node 575644, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_303308_575589, context_13_303309_575619, context_13_303310_575637, context_13_303311_575643.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
