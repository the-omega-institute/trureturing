using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0205Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0205.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0205",
        H("Original frontier context coverage 0205"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09842", "selected_cut_09842", "Selected cut at depth 12, code 24692, node 271036",
                "At remaining fuel 9 and original index 271036, selection on the full partial prefix of depth 12 and code 24692 returns the complete row with depth 12, base-four code 24692, original node 271036, kind 2, reserved field 0, 2685 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09890", "selected_cut_09890", "Selected cut at depth 12, code 24734, node 272264",
                "At remaining fuel 9 and original index 272264, selection on the full partial prefix of depth 12 and code 24734 returns the complete row with depth 12, base-four code 24734, original node 272264, kind 2, reserved field 0, 1833 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-24693-271088", "unmarked_context_12_24693_271088", "Unmarked parent at depth 12, code 24693",
                "The frontier Boolean is false at remaining fuel 9, original node 271088, the whole prefixCache at depth 12 and code 24693, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6182-272196", "unmarked_context_11_6182_272196", "Unmarked parent at depth 11, code 6182",
                "The frontier Boolean is false at remaining fuel 10, original node 272196, the whole prefixCache at depth 11 and code 6182, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-24693-271088", "node_context_12_24693_271088", "Original split at fuel 9 and node 271088",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 271041, 271079, 271087. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6182-272196", "node_context_11_6182_272196", "Original split at fuel 10 and node 272196",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 272125, 272153, 272173, 272195. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-24692-271036", "context_12_24692_271036", "Context at depth 12, code 24692, node 271036",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 24692 and original node 271036, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-24734-272264", "context_12_24734_272264", "Context at depth 12, code 24734, node 272264",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 24734 and original node 272264, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
