using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0746Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0746.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0746",
        H("Original frontier context coverage 0746"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35812", "selected_cut_35812", "Selected cut at depth 12, code 287359, node 943460",
                "At remaining fuel 9 and original index 943460, selection on the full partial prefix of depth 12 and code 287359 returns the complete row with depth 12, base-four code 287359, original node 943460, kind 2, reserved field 0, 1853 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35858", "selected_cut_35858", "Selected cut at depth 11, code 71861, node 944434",
                "At remaining fuel 10 and original index 944434, selection on the full partial prefix of depth 11 and code 71861 returns the complete row with depth 11, base-four code 71861, original node 944434, kind 2, reserved field 0, 1537 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71839-943461", "unmarked_context_11_71839_943461", "Unmarked parent at depth 11, code 71839",
                "The frontier Boolean is false at remaining fuel 10, original node 943461, the whole prefixCache at depth 11 and code 71839, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-17964-944399", "unmarked_context_10_17964_944399", "Unmarked parent at depth 10, code 17964",
                "The frontier Boolean is false at remaining fuel 11, original node 944399, the whole prefixCache at depth 10 and code 17964, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71839-943461", "node_context_11_71839_943461", "Original split at fuel 10 and node 943461",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 943409, 896706, 943431, 943460. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-17964-944399", "node_context_10_17964_944399", "Original split at fuel 11 and node 944399",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 944353, 944370, 944398. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-287359-943460", "context_12_287359_943460", "Context at depth 12, code 287359, node 943460",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287359 and original node 943460, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-71861-944434", "context_11_71861_944434", "Context at depth 11, code 71861, node 944434",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71861 and original node 944434, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
