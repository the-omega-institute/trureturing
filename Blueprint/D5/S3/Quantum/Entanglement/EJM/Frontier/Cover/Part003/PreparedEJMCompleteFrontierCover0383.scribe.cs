using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0383Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0383.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0383",
        H("Original frontier context coverage 0383"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18387", "selected_cut_18387", "Selected cut at depth 8, code 279, node 14298",
                "At remaining fuel 13 and original index 14298, selection on the full partial prefix of depth 8 and code 279 returns the complete row with depth 8, base-four code 279, original node 14298, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16777216. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18434", "selected_cut_18434", "Selected cut at depth 13, code 286799, node 472199",
                "At remaining fuel 8 and original index 472199, selection on the full partial prefix of depth 13 and code 286799 returns the complete row with depth 13, base-four code 286799, original node 472199, kind 2, reserved field 0, 677 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-1115-470521", "unmarked_context_9_1115_470521", "Unmarked parent at depth 9, code 1115",
                "The frontier Boolean is false at remaining fuel 12, original node 470521, the whole prefixCache at depth 9 and code 1115, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71698-472091", "unmarked_context_12_71698_472091", "Unmarked parent at depth 12, code 71698",
                "The frontier Boolean is false at remaining fuel 9, original node 472091, the whole prefixCache at depth 12 and code 71698, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-1115-470521", "node_context_9_1115_470521", "Original split at fuel 12 and node 470521",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 470343, 470438, 470494, 470520. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71698-472091", "node_context_12_71698_472091", "Original split at fuel 9 and node 472091",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 472023, 472060, 472081, 472090. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-1115-470521", "context_9_1115_470521", "Context at depth 9, code 1115, node 470521",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 1115 and original node 470521, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_4460_470343, context_10_4461_470438, context_10_4462_470494, context_10_4463_470520.", DescribeRole.Theorem),
            Node("context-13-286799-472199", "context_13_286799_472199", "Context at depth 13, code 286799, node 472199",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 286799 and original node 472199, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
