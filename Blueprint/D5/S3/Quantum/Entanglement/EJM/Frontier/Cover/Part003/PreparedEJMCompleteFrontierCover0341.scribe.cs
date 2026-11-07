using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0341Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0341.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0341",
        H("Original frontier context coverage 0341"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16371", "selected_cut_16371", "Selected cut at depth 13, code 112896, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 112896 returns the complete row with depth 13, base-four code 112896, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16418", "selected_cut_16418", "Selected cut at depth 13, code 112943, node 417633",
                "At remaining fuel 8 and original index 417633, selection on the full partial prefix of depth 13 and code 112943 returns the complete row with depth 13, base-four code 112943, original node 417633, kind 2, reserved field 0, 957 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-440-416577", "unmarked_context_9_440_416577", "Unmarked parent at depth 9, code 440",
                "The frontier Boolean is false at remaining fuel 12, original node 416577, the whole prefixCache at depth 9 and code 440, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-7058-417635", "unmarked_context_11_7058_417635", "Unmarked parent at depth 11, code 7058",
                "The frontier Boolean is false at remaining fuel 10, original node 417635, the whole prefixCache at depth 11 and code 7058, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-440-416577", "node_context_9_440_416577", "Original split at fuel 12 and node 416577",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 412821, 414221, 415480, 416576. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-7058-417635", "node_context_11_7058_417635", "Original split at fuel 10 and node 417635",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 417328, 417431, 417565, 417634. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-440-416577", "context_9_440_416577", "Context at depth 9, code 440, node 416577",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 440 and original node 416577, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_1760_412821, context_10_1761_414221, context_10_1762_415480, context_10_1763_416576.", DescribeRole.Theorem),
            Node("context-11-7058-417635", "context_11_7058_417635", "Context at depth 11, code 7058, node 417635",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 7058 and original node 417635, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_28232_417328, context_12_28233_417431, context_12_28234_417565, context_12_28235_417634.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
