using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0408Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0408.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0408",
        H("Original frontier context coverage 0408"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19588", "selected_cut_19588", "Selected cut at depth 13, code 289021, node 501302",
                "At remaining fuel 8 and original index 501302, selection on the full partial prefix of depth 13 and code 289021 returns the complete row with depth 13, base-four code 289021, original node 501302, kind 2, reserved field 0, 3145 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19634", "selected_cut_19634", "Selected cut at depth 13, code 289076, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 289076 returns the complete row with depth 13, base-four code 289076, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72255-501330", "unmarked_context_12_72255_501330", "Unmarked parent at depth 12, code 72255",
                "The frontier Boolean is false at remaining fuel 9, original node 501330, the whole prefixCache at depth 12 and code 72255, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72268-502244", "unmarked_context_12_72268_502244", "Unmarked parent at depth 12, code 72268",
                "The frontier Boolean is false at remaining fuel 9, original node 502244, the whole prefixCache at depth 12 and code 72268, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72255-501330", "node_context_12_72255_501330", "Original split at fuel 9 and node 501330",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 501263, 501302, 501319, 501329. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72268-502244", "node_context_12_72268_502244", "Original split at fuel 9 and node 502244",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 502217, 502235, 502243. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-289021-501302", "context_13_289021_501302", "Context at depth 13, code 289021, node 501302",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 289021 and original node 501302, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-289076-3444", "context_13_289076_3444", "Context at depth 13, code 289076, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 289076 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
