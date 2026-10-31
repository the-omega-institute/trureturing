using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0148Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0148.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0148",
        H("Original frontier context coverage 0148"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07107", "selected_cut_07107", "Selected cut at depth 13, code 88347, node 207928",
                "At remaining fuel 8 and original index 207928, selection on the full partial prefix of depth 13 and code 88347 returns the complete row with depth 13, base-four code 88347, original node 207928, kind 2, reserved field 0, 1009 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07154", "selected_cut_07154", "Selected cut at depth 13, code 88397, node 208768",
                "At remaining fuel 8 and original index 208768, selection on the full partial prefix of depth 13 and code 88397 returns the complete row with depth 13, base-four code 88397, original node 208768, kind 2, reserved field 0, 1953 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22086-207929", "unmarked_context_12_22086_207929", "Unmarked parent at depth 12, code 22086",
                "The frontier Boolean is false at remaining fuel 9, original node 207929, the whole prefixCache at depth 12 and code 22086, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22098-208743", "unmarked_context_12_22098_208743", "Unmarked parent at depth 12, code 22098",
                "The frontier Boolean is false at remaining fuel 9, original node 208743, the whole prefixCache at depth 12 and code 22098, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22086-207929", "node_context_12_22086_207929", "Original split at fuel 9 and node 207929",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 207900, 207920, 207928. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22098-208743", "node_context_12_22098_208743", "Original split at fuel 9 and node 208743",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 208718, 208736, 208742. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-88347-207928", "context_13_88347_207928", "Context at depth 13, code 88347, node 207928",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88347 and original node 207928, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-88397-208768", "context_13_88397_208768", "Context at depth 13, code 88397, node 208768",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88397 and original node 208768, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
