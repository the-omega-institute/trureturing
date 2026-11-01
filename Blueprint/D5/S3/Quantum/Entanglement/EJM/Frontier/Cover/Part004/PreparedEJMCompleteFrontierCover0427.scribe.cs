using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0427Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0427.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0427",
        H("Original frontier context coverage 0427"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20498", "selected_cut_20498", "Selected cut at depth 12, code 74024, node 435790",
                "At remaining fuel 9 and original index 435790, selection on the full partial prefix of depth 12 and code 74024 returns the complete row with depth 12, base-four code 74024, original node 435790, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20546", "selected_cut_20546", "Selected cut at depth 13, code 296150, node 527002",
                "At remaining fuel 8 and original index 527002, selection on the full partial prefix of depth 13 and code 296150 returns the complete row with depth 13, base-four code 296150, original node 527002, kind 2, reserved field 0, 2625 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-74025-526259", "unmarked_context_12_74025_526259", "Unmarked parent at depth 12, code 74025",
                "The frontier Boolean is false at remaining fuel 9, original node 526259, the whole prefixCache at depth 12 and code 74025, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-74036-526918", "unmarked_context_12_74036_526918", "Unmarked parent at depth 12, code 74036",
                "The frontier Boolean is false at remaining fuel 9, original node 526918, the whole prefixCache at depth 12 and code 74036, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-74025-526259", "node_context_12_74025_526259", "Original split at fuel 9 and node 526259",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 526204, 526226, 526250, 526258. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-74036-526918", "node_context_12_74036_526918", "Original split at fuel 9 and node 526918",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 526867, 526892, 526912, 526917. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-74024-435790", "context_12_74024_435790", "Context at depth 12, code 74024, node 435790",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 74024 and original node 435790, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-296150-527002", "context_13_296150_527002", "Context at depth 13, code 296150, node 527002",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 296150 and original node 527002, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
