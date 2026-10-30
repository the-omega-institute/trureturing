using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0255Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0255.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0255",
        H("Original frontier context coverage 0255"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12243", "selected_cut_12243", "Selected cut at depth 13, code 104463, node 324595",
                "At remaining fuel 8 and original index 324595, selection on the full partial prefix of depth 13 and code 104463 returns the complete row with depth 13, base-four code 104463, original node 324595, kind 2, reserved field 0, 1161 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12290", "selected_cut_12290", "Selected cut at depth 13, code 104504, node 325976",
                "At remaining fuel 8 and original index 325976, selection on the full partial prefix of depth 13 and code 104504 returns the complete row with depth 13, base-four code 104504, original node 325976, kind 2, reserved field 0, 2437 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26115-324596", "unmarked_context_12_26115_324596", "Unmarked parent at depth 12, code 26115",
                "The frontier Boolean is false at remaining fuel 9, original node 324596, the whole prefixCache at depth 12 and code 26115, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26125-325944", "unmarked_context_12_26125_325944", "Unmarked parent at depth 12, code 26125",
                "The frontier Boolean is false at remaining fuel 9, original node 325944, the whole prefixCache at depth 12 and code 26125, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26115-324596", "node_context_12_26115_324596", "Original split at fuel 9 and node 324596",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 324470, 324546, 324582, 324595. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26125-325944", "node_context_12_26125_325944", "Original split at fuel 9 and node 325944",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 325836, 325907, 325933, 325943. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-104463-324595", "context_13_104463_324595", "Context at depth 13, code 104463, node 324595",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104463 and original node 324595, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-104504-325976", "context_13_104504_325976", "Context at depth 13, code 104504, node 325976",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104504 and original node 325976, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
