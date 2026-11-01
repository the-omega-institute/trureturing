using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0760Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0760.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0760",
        H("Original frontier context coverage 0760"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36483", "selected_cut_36483", "Selected cut at depth 12, code 289308, node 1738",
                "At remaining fuel 9 and original index 1738, selection on the full partial prefix of depth 12 and code 289308 returns the complete row with depth 12, base-four code 289308, original node 1738, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36530", "selected_cut_36530", "Selected cut at depth 12, code 289409, node 968544",
                "At remaining fuel 9 and original index 968544, selection on the full partial prefix of depth 12 and code 289409 returns the complete row with depth 12, base-four code 289409, original node 968544, kind 2, reserved field 0, 1573 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-72327-967056", "unmarked_context_11_72327_967056", "Unmarked parent at depth 11, code 72327",
                "The frontier Boolean is false at remaining fuel 10, original node 967056, the whole prefixCache at depth 11 and code 72327, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-4521-968514", "unmarked_context_9_4521_968514", "Unmarked parent at depth 9, code 4521",
                "The frontier Boolean is false at remaining fuel 12, original node 968514, the whole prefixCache at depth 9 and code 4521, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-72327-967056", "node_context_11_72327_967056", "Original split at fuel 10 and node 967056",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 966943, 966996, 967055. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-4521-968514", "node_context_9_4521_968514", "Original split at fuel 12 and node 968514",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 968167, 893098, 968368, 968513. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-289308-1738", "context_12_289308_1738", "Context at depth 12, code 289308, node 1738",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 289308 and original node 1738, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-289409-968544", "context_12_289409_968544", "Context at depth 12, code 289409, node 968544",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 289409 and original node 968544, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
