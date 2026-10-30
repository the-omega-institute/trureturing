using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0162Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0162.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0162",
        H("Original frontier context coverage 0162"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07779", "selected_cut_07779", "Selected cut at depth 13, code 90567, node 222682",
                "At remaining fuel 8 and original index 222682, selection on the full partial prefix of depth 13 and code 90567 returns the complete row with depth 13, base-four code 90567, original node 222682, kind 2, reserved field 0, 1121 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07826", "selected_cut_07826", "Selected cut at depth 12, code 22685, node 224139",
                "At remaining fuel 9 and original index 224139, selection on the full partial prefix of depth 12 and code 22685 returns the complete row with depth 12, base-four code 22685, original node 224139, kind 2, reserved field 0, 2045 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22641-222683", "unmarked_context_12_22641_222683", "Unmarked parent at depth 12, code 22641",
                "The frontier Boolean is false at remaining fuel 9, original node 222683, the whole prefixCache at depth 12 and code 22641, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5670-224098", "unmarked_context_11_5670_224098", "Unmarked parent at depth 11, code 5670",
                "The frontier Boolean is false at remaining fuel 10, original node 224098, the whole prefixCache at depth 11 and code 5670, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22641-222683", "node_context_12_22641_222683", "Original split at fuel 9 and node 222683",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 222643, 222670, 222682. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5670-224098", "node_context_11_5670_224098", "Original split at fuel 10 and node 224098",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 224035, 224054, 224076, 224097. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-90567-222682", "context_13_90567_222682", "Context at depth 13, code 90567, node 222682",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90567 and original node 222682, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-22685-224139", "context_12_22685_224139", "Context at depth 12, code 22685, node 224139",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22685 and original node 224139, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
