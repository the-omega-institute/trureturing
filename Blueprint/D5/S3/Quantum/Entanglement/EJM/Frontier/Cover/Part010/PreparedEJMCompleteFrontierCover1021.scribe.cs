using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1021Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1021.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1021",
        H("Original frontier context coverage 1021"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49012", "selected_cut_49012", "Selected cut at depth 11, code 101326, node 1383033",
                "At remaining fuel 10 and original index 1383033, selection on the full partial prefix of depth 11 and code 101326 returns the complete row with depth 11, base-four code 101326, original node 1383033, kind 2, reserved field 0, 3273 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49058", "selected_cut_49058", "Selected cut at depth 11, code 101387, node 1384764",
                "At remaining fuel 10 and original index 1384764, selection on the full partial prefix of depth 11 and code 101387 returns the complete row with depth 11, base-four code 101387, original node 1384764, kind 2, reserved field 0, 2785 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25331-1383034", "unmarked_context_10_25331_1383034", "Unmarked parent at depth 10, code 25331",
                "The frontier Boolean is false at remaining fuel 11, original node 1383034, the whole prefixCache at depth 10 and code 25331, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25345-1384552", "unmarked_context_10_25345_1384552", "Unmarked parent at depth 10, code 25345",
                "The frontier Boolean is false at remaining fuel 11, original node 1384552, the whole prefixCache at depth 10 and code 25345, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25331-1383034", "node_context_10_25331_1383034", "Original split at fuel 11 and node 1383034",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1382876, 1382967, 1383033, 977886. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25345-1384552", "node_context_10_25345_1384552", "Original split at fuel 11 and node 1384552",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1384412, 451541, 1384481, 1384551. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-101326-1383033", "context_11_101326_1383033", "Context at depth 11, code 101326, node 1383033",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 101326 and original node 1383033, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-101387-1384764", "context_11_101387_1384764", "Context at depth 11, code 101387, node 1384764",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 101387 and original node 1384764, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
