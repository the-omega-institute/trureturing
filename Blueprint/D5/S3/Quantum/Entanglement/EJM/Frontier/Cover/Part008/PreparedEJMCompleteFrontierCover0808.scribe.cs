using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0808Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0808.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0808",
        H("Original frontier context coverage 0808"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38787", "selected_cut_38787", "Selected cut at depth 13, code 1208343, node 1048598",
                "At remaining fuel 8 and original index 1048598, selection on the full partial prefix of depth 13 and code 1208343 returns the complete row with depth 13, base-four code 1208343, original node 1048598, kind 2, reserved field 0, 549 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38834", "selected_cut_38834", "Selected cut at depth 12, code 302114, node 1050403",
                "At remaining fuel 9 and original index 1050403, selection on the full partial prefix of depth 12 and code 302114 returns the complete row with depth 12, base-four code 302114, original node 1050403, kind 2, reserved field 0, 3021 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-302085-1048599", "unmarked_context_12_302085_1048599", "Unmarked parent at depth 12, code 302085",
                "The frontier Boolean is false at remaining fuel 9, original node 1048599, the whole prefixCache at depth 12 and code 302085, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18881-1050284", "unmarked_context_10_18881_1050284", "Unmarked parent at depth 10, code 18881",
                "The frontier Boolean is false at remaining fuel 11, original node 1050284, the whole prefixCache at depth 10 and code 18881, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-302085-1048599", "node_context_12_302085_1048599", "Original split at fuel 9 and node 1048599",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1048543, 1048564, 1048593, 1048598. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18881-1050284", "node_context_10_18881_1050284", "Original split at fuel 11 and node 1050284",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1049518, 1049798, 1050037, 1050283. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1208343-1048598", "context_13_1208343_1048598", "Context at depth 13, code 1208343, node 1048598",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1208343 and original node 1048598, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-302114-1050403", "context_12_302114_1050403", "Context at depth 12, code 302114, node 1050403",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302114 and original node 1050403, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
