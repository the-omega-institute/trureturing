using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0223Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0223.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0223",
        H("Original frontier context coverage 0223"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10707", "selected_cut_10707", "Selected cut at depth 12, code 25188, node 289097",
                "At remaining fuel 9 and original index 289097, selection on the full partial prefix of depth 12 and code 25188 returns the complete row with depth 12, base-four code 25188, original node 289097, kind 2, reserved field 0, 2885 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10754", "selected_cut_10754", "Selected cut at depth 12, code 25226, node 290332",
                "At remaining fuel 9 and original index 290332, selection on the full partial prefix of depth 12 and code 25226 returns the complete row with depth 12, base-four code 25226, original node 290332, kind 2, reserved field 0, 3097 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6296-289063", "unmarked_context_11_6296_289063", "Unmarked parent at depth 11, code 6296",
                "The frontier Boolean is false at remaining fuel 10, original node 289063, the whole prefixCache at depth 11 and code 6296, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6305-290259", "unmarked_context_11_6305_290259", "Unmarked parent at depth 11, code 6305",
                "The frontier Boolean is false at remaining fuel 10, original node 290259, the whole prefixCache at depth 11 and code 6305, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6296-289063", "node_context_11_6296_289063", "Original split at fuel 10 and node 289063",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 288932, 288991, 289021, 289062. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6305-290259", "node_context_11_6305_290259", "Original split at fuel 10 and node 290259",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 290178, 290205, 290232, 290258. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-6296-289063", "context_11_6296_289063", "Context at depth 11, code 6296, node 289063",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6296 and original node 289063, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_25184_288932, context_12_25185_288991, context_12_25186_289021, context_12_25187_289062.", DescribeRole.Theorem),
            Node("context-12-25226-290332", "context_12_25226_290332", "Context at depth 12, code 25226, node 290332",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25226 and original node 290332, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
