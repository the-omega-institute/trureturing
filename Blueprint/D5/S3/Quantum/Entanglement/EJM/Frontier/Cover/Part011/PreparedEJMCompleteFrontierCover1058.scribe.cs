using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1058Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1058.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1058",
        H("Original frontier context coverage 1058"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50788", "selected_cut_50788", "Selected cut at depth 12, code 441106, node 1454788",
                "At remaining fuel 9 and original index 1454788, selection on the full partial prefix of depth 12 and code 441106 returns the complete row with depth 12, base-four code 441106, original node 1454788, kind 2, reserved field 0, 2013 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50834", "selected_cut_50834", "Selected cut at depth 10, code 27584, node 1456499",
                "At remaining fuel 11 and original index 1456499, selection on the full partial prefix of depth 10 and code 27584 returns the complete row with depth 10, base-four code 27584, original node 1456499, kind 2, reserved field 0, 2933 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-110276-1454828", "unmarked_context_11_110276_1454828", "Unmarked parent at depth 11, code 110276",
                "The frontier Boolean is false at remaining fuel 10, original node 1454828, the whole prefixCache at depth 11 and code 110276, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-7-430-1456366", "unmarked_context_7_430_1456366", "Unmarked parent at depth 7, code 430",
                "The frontier Boolean is false at remaining fuel 14, original node 1456366, the whole prefixCache at depth 7 and code 430, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-110276-1454828", "node_context_11_110276_1454828", "Original split at fuel 10 and node 1454828",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1454742, 1454788, 1454827. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-7-430-1456366", "node_context_7_430_1456366", "Original split at fuel 14 and node 1456366",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 1450487, 1452755, 1454555, 1456365. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-441106-1454788", "context_12_441106_1454788", "Context at depth 12, code 441106, node 1454788",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 441106 and original node 1454788, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-27584-1456499", "context_10_27584_1456499", "Context at depth 10, code 27584, node 1456499",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 27584 and original node 1456499, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
