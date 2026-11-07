using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0343Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0343.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0343",
        H("Original frontier context coverage 0343"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16468", "selected_cut_16468", "Selected cut at depth 12, code 28252, node 418530",
                "At remaining fuel 9 and original index 418530, selection on the full partial prefix of depth 12 and code 28252 returns the complete row with depth 12, base-four code 28252, original node 418530, kind 2, reserved field 0, 3353 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16515", "selected_cut_16515", "Selected cut at depth 12, code 28278, node 419938",
                "At remaining fuel 9 and original index 419938, selection on the full partial prefix of depth 12 and code 28278 returns the complete row with depth 12, base-four code 28278, original node 419938, kind 2, reserved field 0, 2965 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-7062-418491", "unmarked_context_11_7062_418491", "Unmarked parent at depth 11, code 7062",
                "The frontier Boolean is false at remaining fuel 10, original node 418491, the whole prefixCache at depth 11 and code 7062, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-7068-419766", "unmarked_context_11_7068_419766", "Unmarked parent at depth 11, code 7068",
                "The frontier Boolean is false at remaining fuel 10, original node 419766, the whole prefixCache at depth 11 and code 7068, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-7062-418491", "node_context_11_7062_418491", "Original split at fuel 10 and node 418491",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 418347, 126371, 418434, 418490. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-7068-419766", "node_context_11_7068_419766", "Original split at fuel 10 and node 419766",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 419596, 419682, 419719, 419765. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-7062-418491", "context_11_7062_418491", "Context at depth 11, code 7062, node 418491",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 7062 and original node 418491, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_28248_418347, context_12_28249_126371, context_12_28250_418434, context_12_28251_418490.", DescribeRole.Theorem),
            Node("context-12-28278-419938", "context_12_28278_419938", "Context at depth 12, code 28278, node 419938",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28278 and original node 419938, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
