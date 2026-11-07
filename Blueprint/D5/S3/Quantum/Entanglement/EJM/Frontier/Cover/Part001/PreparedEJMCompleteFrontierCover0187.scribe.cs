using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0187Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0187.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0187",
        H("Original frontier context coverage 0187"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08979", "selected_cut_08979", "Selected cut at depth 12, code 23217, node 249172",
                "At remaining fuel 9 and original index 249172, selection on the full partial prefix of depth 12 and code 23217 returns the complete row with depth 12, base-four code 23217, original node 249172, kind 2, reserved field 0, 1449 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09026", "selected_cut_09026", "Selected cut at depth 13, code 93194, node 250283",
                "At remaining fuel 8 and original index 250283, selection on the full partial prefix of depth 13 and code 93194 returns the complete row with depth 13, base-four code 93194, original node 250283, kind 2, reserved field 0, 765 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5804-249205", "unmarked_context_11_5804_249205", "Unmarked parent at depth 11, code 5804",
                "The frontier Boolean is false at remaining fuel 10, original node 249205, the whole prefixCache at depth 11 and code 5804, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-93192-250124", "unmarked_context_13_93192_250124", "Unmarked parent at depth 13, code 93192",
                "The frontier Boolean is false at remaining fuel 8, original node 250124, the whole prefixCache at depth 13 and code 93192, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5804-249205", "node_context_11_5804_249205", "Original split at fuel 10 and node 249205",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 249156, 249172, 249187, 249204. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-93192-250124", "node_context_13_93192_250124", "Original split at fuel 8 and node 250124",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 250048, 250064, 250099, 250123. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-23217-249172", "context_12_23217_249172", "Context at depth 12, code 23217, node 249172",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23217 and original node 249172, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-93194-250283", "context_13_93194_250283", "Context at depth 13, code 93194, node 250283",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93194 and original node 250283, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
