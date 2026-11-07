using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0089Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0089.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0089",
        H("Original frontier context coverage 0089"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04275", "selected_cut_04275", "Selected cut at depth 10, code 1128, node 3442",
                "At remaining fuel 11 and original index 3442, selection on the full partial prefix of depth 10 and code 1128 returns the complete row with depth 10, base-four code 1128, original node 3442, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04321", "selected_cut_04321", "Selected cut at depth 14, code 294967, node 137476",
                "At remaining fuel 7 and original index 137476, selection on the full partial prefix of depth 14 and code 294967 returns the complete row with depth 14, base-four code 294967, original node 137476, kind 2, reserved field 0, 1357 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1127-135596", "unmarked_context_10_1127_135596", "Unmarked parent at depth 10, code 1127",
                "The frontier Boolean is false at remaining fuel 11, original node 135596, the whole prefixCache at depth 10 and code 1127, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-73741-137477", "unmarked_context_13_73741_137477", "Unmarked parent at depth 13, code 73741",
                "The frontier Boolean is false at remaining fuel 8, original node 137477, the whole prefixCache at depth 13 and code 73741, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1127-135596", "node_context_10_1127_135596", "Original split at fuel 11 and node 135596",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 135124, 135302, 135463, 135595. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-73741-137477", "node_context_13_73741_137477", "Original split at fuel 8 and node 137477",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 137377, 137413, 137451, 137476. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-1127-135596", "context_10_1127_135596", "Context at depth 10, code 1127, node 135596",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1127 and original node 135596, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_4508_135124, context_11_4509_135302, context_11_4510_135463, context_11_4511_135595.", DescribeRole.Theorem),
            Node("context-13-73741-137477", "context_13_73741_137477", "Context at depth 13, code 73741, node 137477",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 73741 and original node 137477, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_294964_137377, context_14_294965_137413, context_14_294966_137451, context_14_294967_137476.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
