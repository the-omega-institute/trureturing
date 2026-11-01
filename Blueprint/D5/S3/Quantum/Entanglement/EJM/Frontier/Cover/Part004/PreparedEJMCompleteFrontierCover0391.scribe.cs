using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0391Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0391.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0391",
        H("Original frontier context coverage 0391"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18771", "selected_cut_18771", "Selected cut at depth 12, code 71862, node 479882",
                "At remaining fuel 9 and original index 479882, selection on the full partial prefix of depth 12 and code 71862 returns the complete row with depth 12, base-four code 71862, original node 479882, kind 2, reserved field 0, 1365 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18818", "selected_cut_18818", "Selected cut at depth 14, code 1151090, node 481469",
                "At remaining fuel 7 and original index 481469, selection on the full partial prefix of depth 14 and code 1151090 returns the complete row with depth 14, base-four code 1151090, original node 481469, kind 2, reserved field 0, 1725 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-17965-479894", "unmarked_context_11_17965_479894", "Unmarked parent at depth 11, code 17965",
                "The frontier Boolean is false at remaining fuel 10, original node 479894, the whole prefixCache at depth 11 and code 17965, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71942-481386", "unmarked_context_12_71942_481386", "Unmarked parent at depth 12, code 71942",
                "The frontier Boolean is false at remaining fuel 9, original node 481386, the whole prefixCache at depth 12 and code 71942, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-17965-479894", "node_context_11_17965_479894", "Original split at fuel 10 and node 479894",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 479849, 479865, 479882, 479893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71942-481386", "node_context_12_71942_481386", "Original split at fuel 9 and node 481386",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 481155, 481269, 481349, 481385. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-71862-479882", "context_12_71862_479882", "Context at depth 12, code 71862, node 479882",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71862 and original node 479882, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-1151090-481469", "context_14_1151090_481469", "Context at depth 14, code 1151090, node 481469",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 1151090 and original node 481469, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
