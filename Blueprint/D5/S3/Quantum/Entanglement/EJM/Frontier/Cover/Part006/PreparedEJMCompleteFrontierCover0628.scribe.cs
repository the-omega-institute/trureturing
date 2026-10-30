using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0628Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0628.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0628",
        H("Original frontier context coverage 0628"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30148", "selected_cut_30148", "Selected cut at depth 12, code 94042, node 760896",
                "At remaining fuel 9 and original index 760896, selection on the full partial prefix of depth 12 and code 94042 returns the complete row with depth 12, base-four code 94042, original node 760896, kind 2, reserved field 0, 3097 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30195", "selected_cut_30195", "Selected cut at depth 12, code 94086, node 762289",
                "At remaining fuel 9 and original index 762289, selection on the full partial prefix of depth 12 and code 94086 returns the complete row with depth 12, base-four code 94086, original node 762289, kind 2, reserved field 0, 2249 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23510-760942", "unmarked_context_11_23510_760942", "Unmarked parent at depth 11, code 23510",
                "The frontier Boolean is false at remaining fuel 10, original node 760942, the whole prefixCache at depth 11 and code 23510, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23520-762212", "unmarked_context_11_23520_762212", "Unmarked parent at depth 11, code 23520",
                "The frontier Boolean is false at remaining fuel 10, original node 762212, the whole prefixCache at depth 11 and code 23520, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23510-760942", "node_context_11_23510_760942", "Original split at fuel 10 and node 760942",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 760856, 642341, 760896, 760941. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23520-762212", "node_context_11_23520_762212", "Original split at fuel 10 and node 762212",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 762141, 762163, 762184, 762211. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-94042-760896", "context_12_94042_760896", "Context at depth 12, code 94042, node 760896",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 94042 and original node 760896, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-94086-762289", "context_12_94086_762289", "Context at depth 12, code 94086, node 762289",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 94086 and original node 762289, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
