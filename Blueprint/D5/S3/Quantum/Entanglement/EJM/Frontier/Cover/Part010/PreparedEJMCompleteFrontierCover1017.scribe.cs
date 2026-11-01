using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1017Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1017.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1017",
        H("Original frontier context coverage 1017"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48819", "selected_cut_48819", "Selected cut at depth 11, code 100836, node 1373229",
                "At remaining fuel 10 and original index 1373229, selection on the full partial prefix of depth 11 and code 100836 returns the complete row with depth 11, base-four code 100836, original node 1373229, kind 2, reserved field 0, 2729 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48866", "selected_cut_48866", "Selected cut at depth 11, code 100955, node 1375532",
                "At remaining fuel 10 and original index 1375532, selection on the full partial prefix of depth 11 and code 100955 returns the complete row with depth 11, base-four code 100955, original node 1375532, kind 2, reserved field 0, 2013 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25209-1373322", "unmarked_context_10_25209_1373322", "Unmarked parent at depth 10, code 25209",
                "The frontier Boolean is false at remaining fuel 11, original node 1373322, the whole prefixCache at depth 10 and code 25209, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25238-1375533", "unmarked_context_10_25238_1375533", "Unmarked parent at depth 10, code 25238",
                "The frontier Boolean is false at remaining fuel 11, original node 1375533, the whole prefixCache at depth 10 and code 25238, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25209-1373322", "node_context_10_25209_1373322", "Original split at fuel 11 and node 1373322",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1373229, 892405, 1373277, 1373321. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25238-1375533", "node_context_10_25238_1375533", "Original split at fuel 11 and node 1375533",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1375389, 1375461, 1375264, 1375532. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-100836-1373229", "context_11_100836_1373229", "Context at depth 11, code 100836, node 1373229",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 100836 and original node 1373229, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-25238-1375533", "context_10_25238_1375533", "Context at depth 10, code 25238, node 1375533",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25238 and original node 1375533, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_100952_1375389, context_11_100953_1375461, context_11_100954_1375264, context_11_100955_1375532.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
