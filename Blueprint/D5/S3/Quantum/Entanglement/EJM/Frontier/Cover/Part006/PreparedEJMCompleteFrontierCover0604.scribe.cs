using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0604Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0604.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0604",
        H("Original frontier context coverage 0604"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28995", "selected_cut_28995", "Selected cut at depth 13, code 372897, node 732385",
                "At remaining fuel 8 and original index 732385, selection on the full partial prefix of depth 13 and code 372897 returns the complete row with depth 13, base-four code 372897, original node 732385, kind 2, reserved field 0, 1741 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29043", "selected_cut_29043", "Selected cut at depth 13, code 372951, node 733293",
                "At remaining fuel 8 and original index 733293, selection on the full partial prefix of depth 13 and code 372951 returns the complete row with depth 13, base-four code 372951, original node 733293, kind 2, reserved field 0, 773 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93224-732418", "unmarked_context_12_93224_732418", "Unmarked parent at depth 12, code 93224",
                "The frontier Boolean is false at remaining fuel 9, original node 732418, the whole prefixCache at depth 12 and code 93224, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93236-733226", "unmarked_context_12_93236_733226", "Unmarked parent at depth 12, code 93236",
                "The frontier Boolean is false at remaining fuel 9, original node 733226, the whole prefixCache at depth 12 and code 93236, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93224-732418", "node_context_12_93224_732418", "Original split at fuel 9 and node 732418",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 732356, 732385, 732407, 732417. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93236-733226", "node_context_12_93236_733226", "Original split at fuel 9 and node 733226",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 733168, 733195, 733216, 733225. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-372897-732385", "context_13_372897_732385", "Context at depth 13, code 372897, node 732385",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 372897 and original node 732385, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-372951-733293", "context_13_372951_733293", "Context at depth 13, code 372951, node 733293",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 372951 and original node 733293, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
