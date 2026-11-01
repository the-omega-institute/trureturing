using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0641Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0641.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0641",
        H("Original frontier context coverage 0641"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30772", "selected_cut_30772", "Selected cut at depth 11, code 26266, node 782050",
                "At remaining fuel 10 and original index 782050, selection on the full partial prefix of depth 11 and code 26266 returns the complete row with depth 11, base-four code 26266, original node 782050, kind 2, reserved field 0, 5 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30818", "selected_cut_30818", "Selected cut at depth 13, code 420935, node 783510",
                "At remaining fuel 8 and original index 783510, selection on the full partial prefix of depth 13 and code 420935 returns the complete row with depth 13, base-four code 420935, original node 783510, kind 2, reserved field 0, 685 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26265-782048", "unmarked_context_11_26265_782048", "Unmarked parent at depth 11, code 26265",
                "The frontier Boolean is false at remaining fuel 10, original node 782048, the whole prefixCache at depth 11 and code 26265, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-105233-783511", "unmarked_context_12_105233_783511", "Unmarked parent at depth 12, code 105233",
                "The frontier Boolean is false at remaining fuel 9, original node 783511, the whole prefixCache at depth 12 and code 105233, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26265-782048", "node_context_11_26265_782048", "Original split at fuel 10 and node 782048",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 781942, 781975, 782004, 782047. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-105233-783511", "node_context_12_105233_783511", "Original split at fuel 9 and node 783511",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 783440, 783474, 783502, 783510. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-26265-782048", "context_11_26265_782048", "Context at depth 11, code 26265, node 782048",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 26265 and original node 782048, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_105060_781942, context_12_105061_781975, context_12_105062_782004, context_12_105063_782047.", DescribeRole.Theorem),
            Node("context-12-105233-783511", "context_12_105233_783511", "Context at depth 12, code 105233, node 783511",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105233 and original node 783511, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_420932_783440, context_13_420933_783474, context_13_420934_783502, context_13_420935_783510.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
