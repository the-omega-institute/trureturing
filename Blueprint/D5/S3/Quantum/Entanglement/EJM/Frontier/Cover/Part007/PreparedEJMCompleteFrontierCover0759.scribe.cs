using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0759Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0759.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0759",
        H("Original frontier context coverage 0759"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36436", "selected_cut_36436", "Selected cut at depth 11, code 72175, node 965232",
                "At remaining fuel 10 and original index 965232, selection on the full partial prefix of depth 11 and code 72175 returns the complete row with depth 11, base-four code 72175, original node 965232, kind 2, reserved field 0, 2217 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36482", "selected_cut_36482", "Selected cut at depth 12, code 289307, node 966887",
                "At remaining fuel 9 and original index 966887, selection on the full partial prefix of depth 12 and code 289307 returns the complete row with depth 12, base-four code 289307, original node 966887, kind 2, reserved field 0, 3265 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-18043-965233", "unmarked_context_10_18043_965233", "Unmarked parent at depth 10, code 18043",
                "The frontier Boolean is false at remaining fuel 11, original node 965233, the whole prefixCache at depth 10 and code 18043, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-72326-966888", "unmarked_context_11_72326_966888", "Unmarked parent at depth 11, code 72326",
                "The frontier Boolean is false at remaining fuel 10, original node 966888, the whole prefixCache at depth 11 and code 72326, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-18043-965233", "node_context_10_18043_965233", "Original split at fuel 11 and node 965233",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 965082, 965138, 965194, 965232. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-72326-966888", "node_context_11_72326_966888", "Original split at fuel 10 and node 966888",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 966820, 893903, 966887. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-72175-965232", "context_11_72175_965232", "Context at depth 11, code 72175, node 965232",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 72175 and original node 965232, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-72326-966888", "context_11_72326_966888", "Context at depth 11, code 72326, node 966888",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 72326 and original node 966888, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_289304_1738, context_12_289305_966820, context_12_289306_893903, context_12_289307_966887.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
