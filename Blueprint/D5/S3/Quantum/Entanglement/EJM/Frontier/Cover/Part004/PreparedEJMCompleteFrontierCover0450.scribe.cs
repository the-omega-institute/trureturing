using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0450Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0450.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0450",
        H("Original frontier context coverage 0450"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21602", "selected_cut_21602", "Selected cut at depth 12, code 75104, node 552155",
                "At remaining fuel 9 and original index 552155, selection on the full partial prefix of depth 12 and code 75104 returns the complete row with depth 12, base-four code 75104, original node 552155, kind 2, reserved field 0, 3557 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21650", "selected_cut_21650", "Selected cut at depth 12, code 75146, node 553952",
                "At remaining fuel 9 and original index 553952, selection on the full partial prefix of depth 12 and code 75146 returns the complete row with depth 12, base-four code 75146, original node 553952, kind 2, reserved field 0, 2569 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75106-552246", "unmarked_context_12_75106_552246", "Unmarked parent at depth 12, code 75106",
                "The frontier Boolean is false at remaining fuel 9, original node 552246, the whole prefixCache at depth 12 and code 75106, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18785-553830", "unmarked_context_11_18785_553830", "Unmarked parent at depth 11, code 18785",
                "The frontier Boolean is false at remaining fuel 10, original node 553830, the whole prefixCache at depth 11 and code 18785, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75106-552246", "node_context_12_75106_552246", "Original split at fuel 9 and node 552246",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 552211, 552237, 552245. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18785-553830", "node_context_11_18785_553830", "Original split at fuel 10 and node 553830",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 553701, 553763, 553794, 553829. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75104-552155", "context_12_75104_552155", "Context at depth 12, code 75104, node 552155",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75104 and original node 552155, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-75146-553952", "context_12_75146_553952", "Context at depth 12, code 75146, node 553952",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75146 and original node 553952, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
