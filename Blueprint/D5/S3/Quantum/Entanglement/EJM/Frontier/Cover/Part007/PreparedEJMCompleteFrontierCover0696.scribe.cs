using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0696Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0696.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0696",
        H("Original frontier context coverage 0696"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33412", "selected_cut_33412", "Selected cut at depth 12, code 110194, node 860091",
                "At remaining fuel 9 and original index 860091, selection on the full partial prefix of depth 12 and code 110194 returns the complete row with depth 12, base-four code 110194, original node 860091, kind 2, reserved field 0, 2165 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33459", "selected_cut_33459", "Selected cut at depth 12, code 110244, node 861179",
                "At remaining fuel 9 and original index 861179, selection on the full partial prefix of depth 12 and code 110244 returns the complete row with depth 12, base-four code 110244, original node 861179, kind 2, reserved field 0, 1345 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-27548-860134", "unmarked_context_11_27548_860134", "Unmarked parent at depth 11, code 27548",
                "The frontier Boolean is false at remaining fuel 10, original node 860134, the whole prefixCache at depth 11 and code 27548, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27560-861164", "unmarked_context_11_27560_861164", "Unmarked parent at depth 11, code 27560",
                "The frontier Boolean is false at remaining fuel 10, original node 861164, the whole prefixCache at depth 11 and code 27560, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-27548-860134", "node_context_11_27548_860134", "Original split at fuel 10 and node 860134",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 860027, 860061, 860091, 860133. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27560-861164", "node_context_11_27560_861164", "Original split at fuel 10 and node 861164",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 861125, 861144, 769937, 861163. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-110194-860091", "context_12_110194_860091", "Context at depth 12, code 110194, node 860091",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 110194 and original node 860091, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-110244-861179", "context_12_110244_861179", "Context at depth 12, code 110244, node 861179",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 110244 and original node 861179, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
