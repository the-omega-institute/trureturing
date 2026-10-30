using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1073Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1073.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1073",
        H("Original frontier context coverage 1073"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51507", "selected_cut_51507", "Selected cut at depth 11, code 281541, node 1468419",
                "At remaining fuel 10 and original index 1468419, selection on the full partial prefix of depth 11 and code 281541 returns the complete row with depth 11, base-four code 281541, original node 1468419, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51553", "selected_cut_51553", "Selected cut at depth 10, code 70696, node 1488444",
                "At remaining fuel 11 and original index 1488444, selection on the full partial prefix of depth 10 and code 70696 returns the complete row with depth 10, base-four code 70696, original node 1488444, kind 2, reserved field 0, 1917 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-70385-1486511", "unmarked_context_10_70385_1486511", "Unmarked parent at depth 10, code 70385",
                "The frontier Boolean is false at remaining fuel 11, original node 1486511, the whole prefixCache at depth 10 and code 70385, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-17673-1488409", "unmarked_context_9_17673_1488409", "Unmarked parent at depth 9, code 17673",
                "The frontier Boolean is false at remaining fuel 12, original node 1488409, the whole prefixCache at depth 9 and code 17673, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-70385-1486511", "node_context_10_70385_1486511", "Original split at fuel 11 and node 1486511",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1486307, 1468419, 1486463, 1486510. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-17673-1488409", "node_context_9_17673_1488409", "Original split at fuel 12 and node 1488409",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1488179, 1468874, 1488308, 1488408. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-281541-1468419", "context_11_281541_1468419", "Context at depth 11, code 281541, node 1468419",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 281541 and original node 1468419, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-70696-1488444", "context_10_70696_1488444", "Context at depth 10, code 70696, node 1488444",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 70696 and original node 1488444, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
