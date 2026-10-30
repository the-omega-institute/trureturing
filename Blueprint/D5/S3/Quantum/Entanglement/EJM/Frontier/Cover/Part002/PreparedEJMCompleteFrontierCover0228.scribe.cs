using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0228Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0228.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0228",
        H("Original frontier context coverage 0228"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10947", "selected_cut_10947", "Selected cut at depth 13, code 101526, node 294935",
                "At remaining fuel 8 and original index 294935, selection on the full partial prefix of depth 13 and code 101526 returns the complete row with depth 13, base-four code 101526, original node 294935, kind 2, reserved field 0, 1345 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10994", "selected_cut_10994", "Selected cut at depth 13, code 101576, node 295764",
                "At remaining fuel 8 and original index 295764, selection on the full partial prefix of depth 13 and code 101576 returns the complete row with depth 13, base-four code 101576, original node 295764, kind 2, reserved field 0, 389 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25381-294942", "unmarked_context_12_25381_294942", "Unmarked parent at depth 12, code 25381",
                "The frontier Boolean is false at remaining fuel 9, original node 294942, the whole prefixCache at depth 12 and code 25381, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25393-295756", "unmarked_context_12_25393_295756", "Unmarked parent at depth 12, code 25393",
                "The frontier Boolean is false at remaining fuel 9, original node 295756, the whole prefixCache at depth 12 and code 25393, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25381-294942", "node_context_12_25381_294942", "Original split at fuel 9 and node 294942",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 294892, 294917, 294935, 294941. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25393-295756", "node_context_12_25393_295756", "Original split at fuel 9 and node 295756",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 295706, 295730, 295749, 295755. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-101526-294935", "context_13_101526_294935", "Context at depth 13, code 101526, node 294935",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 101526 and original node 294935, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-101576-295764", "context_13_101576_295764", "Context at depth 13, code 101576, node 295764",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 101576 and original node 295764, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
