using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0185Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0185.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0185",
        H("Original frontier context coverage 0185"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08884", "selected_cut_08884", "Selected cut at depth 13, code 92575, node 246864",
                "At remaining fuel 8 and original index 246864, selection on the full partial prefix of depth 13 and code 92575 returns the complete row with depth 13, base-four code 92575, original node 246864, kind 2, reserved field 0, 957 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08931", "selected_cut_08931", "Selected cut at depth 12, code 23166, node 247985",
                "At remaining fuel 9 and original index 247985, selection on the full partial prefix of depth 12 and code 23166 returns the complete row with depth 12, base-four code 23166, original node 247985, kind 2, reserved field 0, 2901 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23143-246865", "unmarked_context_12_23143_246865", "Unmarked parent at depth 12, code 23143",
                "The frontier Boolean is false at remaining fuel 9, original node 246865, the whole prefixCache at depth 12 and code 23143, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5790-247863", "unmarked_context_11_5790_247863", "Unmarked parent at depth 11, code 5790",
                "The frontier Boolean is false at remaining fuel 10, original node 247863, the whole prefixCache at depth 11 and code 5790, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23143-246865", "node_context_12_23143_246865", "Original split at fuel 9 and node 246865",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 246831, 246853, 246864. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5790-247863", "node_context_11_5790_247863", "Original split at fuel 10 and node 247863",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 247662, 247705, 247817, 247862. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-92575-246864", "context_13_92575_246864", "Context at depth 13, code 92575, node 246864",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92575 and original node 246864, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-23166-247985", "context_12_23166_247985", "Context at depth 12, code 23166, node 247985",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23166 and original node 247985, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
