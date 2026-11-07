using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0727Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0727.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0727",
        H("Original frontier context coverage 0727"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34898", "selected_cut_34898", "Selected cut at depth 12, code 283142, node 911846",
                "At remaining fuel 9 and original index 911846, selection on the full partial prefix of depth 12 and code 283142 returns the complete row with depth 12, base-four code 283142, original node 911846, kind 2, reserved field 0, 3201 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34946", "selected_cut_34946", "Selected cut at depth 12, code 283181, node 914255",
                "At remaining fuel 9 and original index 914255, selection on the full partial prefix of depth 12 and code 283181 returns the complete row with depth 12, base-four code 283181, original node 914255, kind 2, reserved field 0, 3729 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-70785-911912", "unmarked_context_11_70785_911912", "Unmarked parent at depth 11, code 70785",
                "The frontier Boolean is false at remaining fuel 10, original node 911912, the whole prefixCache at depth 11 and code 70785, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-70794-914115", "unmarked_context_11_70794_914115", "Unmarked parent at depth 11, code 70794",
                "The frontier Boolean is false at remaining fuel 10, original node 914115, the whole prefixCache at depth 11 and code 70794, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-70785-911912", "node_context_11_70785_911912", "Original split at fuel 10 and node 911912",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 911723, 911781, 911846, 911911. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-70794-914115", "node_context_11_70794_914115", "Original split at fuel 10 and node 914115",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 913972, 914044, 242157, 914114. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-283142-911846", "context_12_283142_911846", "Context at depth 12, code 283142, node 911846",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 283142 and original node 911846, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-283181-914255", "context_12_283181_914255", "Context at depth 12, code 283181, node 914255",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 283181 and original node 914255, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
