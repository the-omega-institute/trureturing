using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0465Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0465.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0465",
        H("Original frontier context coverage 0465"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22323", "selected_cut_22323", "Selected cut at depth 13, code 302343, node 568277",
                "At remaining fuel 8 and original index 568277, selection on the full partial prefix of depth 13 and code 302343 returns the complete row with depth 13, base-four code 302343, original node 568277, kind 2, reserved field 0, 585 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22371", "selected_cut_22371", "Selected cut at depth 13, code 302397, node 569214",
                "At remaining fuel 8 and original index 569214, selection on the full partial prefix of depth 13 and code 302397 returns the complete row with depth 13, base-four code 302397, original node 569214, kind 2, reserved field 0, 3541 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75585-568278", "unmarked_context_12_75585_568278", "Unmarked parent at depth 12, code 75585",
                "The frontier Boolean is false at remaining fuel 9, original node 568278, the whole prefixCache at depth 12 and code 75585, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75598-569148", "unmarked_context_12_75598_569148", "Unmarked parent at depth 12, code 75598",
                "The frontier Boolean is false at remaining fuel 9, original node 569148, the whole prefixCache at depth 12 and code 75598, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75585-568278", "node_context_12_75585_568278", "Original split at fuel 9 and node 568278",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 568254, 568273, 568277. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75598-569148", "node_context_12_75598_569148", "Original split at fuel 9 and node 569148",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 569120, 569139, 569147. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-302343-568277", "context_13_302343_568277", "Context at depth 13, code 302343, node 568277",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302343 and original node 568277, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-302397-569214", "context_13_302397_569214", "Context at depth 13, code 302397, node 569214",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302397 and original node 569214, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
