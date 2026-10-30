using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0195Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0195.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0195",
        H("Original frontier context coverage 0195"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09363", "selected_cut_09363", "Selected cut at depth 13, code 93462, node 258478",
                "At remaining fuel 8 and original index 258478, selection on the full partial prefix of depth 13 and code 93462 returns the complete row with depth 13, base-four code 93462, original node 258478, kind 2, reserved field 0, 2029 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09410", "selected_cut_09410", "Selected cut at depth 13, code 93512, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 93512 returns the complete row with depth 13, base-four code 93512, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23365-258495", "unmarked_context_12_23365_258495", "Unmarked parent at depth 12, code 23365",
                "The frontier Boolean is false at remaining fuel 9, original node 258495, the whole prefixCache at depth 12 and code 23365, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23376-259657", "unmarked_context_12_23376_259657", "Unmarked parent at depth 12, code 23376",
                "The frontier Boolean is false at remaining fuel 9, original node 259657, the whole prefixCache at depth 12 and code 23376, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23365-258495", "node_context_12_23365_258495", "Original split at fuel 9 and node 258495",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 258453, 258478, 258494. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23376-259657", "node_context_12_23376_259657", "Original split at fuel 9 and node 259657",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 259624, 259645, 259656. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-93462-258478", "context_13_93462_258478", "Context at depth 13, code 93462, node 258478",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93462 and original node 258478, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-93512-3444", "context_13_93512_3444", "Context at depth 13, code 93512, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93512 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
