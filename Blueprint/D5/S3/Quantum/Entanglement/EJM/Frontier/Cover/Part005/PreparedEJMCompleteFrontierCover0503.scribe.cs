using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0503Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0503.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0503",
        H("Original frontier context coverage 0503"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24147", "selected_cut_24147", "Selected cut at depth 12, code 76917, node 610473",
                "At remaining fuel 9 and original index 610473, selection on the full partial prefix of depth 12 and code 76917 returns the complete row with depth 12, base-four code 76917, original node 610473, kind 2, reserved field 0, 3333 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24194", "selected_cut_24194", "Selected cut at depth 12, code 76964, node 612109",
                "At remaining fuel 9 and original index 612109, selection on the full partial prefix of depth 12 and code 76964 returns the complete row with depth 12, base-four code 76964, original node 612109, kind 2, reserved field 0, 1701 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19229-610566", "unmarked_context_11_19229_610566", "Unmarked parent at depth 11, code 19229",
                "The frontier Boolean is false at remaining fuel 10, original node 610566, the whole prefixCache at depth 11 and code 19229, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19240-612090", "unmarked_context_11_19240_612090", "Unmarked parent at depth 11, code 19240",
                "The frontier Boolean is false at remaining fuel 10, original node 612090, the whole prefixCache at depth 11 and code 19240, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19229-610566", "node_context_11_19229_610566", "Original split at fuel 10 and node 610566",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 610435, 610473, 610512, 610565. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19240-612090", "node_context_11_19240_612090", "Original split at fuel 10 and node 612090",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 544742, 612053, 612070, 612089. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76917-610473", "context_12_76917_610473", "Context at depth 12, code 76917, node 610473",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76917 and original node 610473, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-76964-612109", "context_12_76964_612109", "Context at depth 12, code 76964, node 612109",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76964 and original node 612109, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
