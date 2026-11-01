using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0444Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0444.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0444",
        H("Original frontier context coverage 0444"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21314", "selected_cut_21314", "Selected cut at depth 11, code 18737, node 545303",
                "At remaining fuel 10 and original index 545303, selection on the full partial prefix of depth 11 and code 18737 returns the complete row with depth 11, base-four code 18737, original node 545303, kind 2, reserved field 0, 2637 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21361", "selected_cut_21361", "Selected cut at depth 13, code 300100, node 546737",
                "At remaining fuel 8 and original index 546737, selection on the full partial prefix of depth 13 and code 300100 returns the complete row with depth 13, base-four code 300100, original node 546737, kind 2, reserved field 0, 1349 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-4684-545362", "unmarked_context_10_4684_545362", "Unmarked parent at depth 10, code 4684",
                "The frontier Boolean is false at remaining fuel 11, original node 545362, the whole prefixCache at depth 10 and code 4684, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4688-546713", "unmarked_context_10_4688_546713", "Unmarked parent at depth 10, code 4688",
                "The frontier Boolean is false at remaining fuel 11, original node 546713, the whole prefixCache at depth 10 and code 4688, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-4684-545362", "node_context_10_4684_545362", "Original split at fuel 11 and node 545362",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 545276, 545303, 545330, 545361. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4688-546713", "node_context_10_4688_546713", "Original split at fuel 11 and node 546713",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 545943, 546406, 546712. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-18737-545303", "context_11_18737_545303", "Context at depth 11, code 18737, node 545303",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18737 and original node 545303, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-300100-546737", "context_13_300100_546737", "Context at depth 13, code 300100, node 546737",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 300100 and original node 546737, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
