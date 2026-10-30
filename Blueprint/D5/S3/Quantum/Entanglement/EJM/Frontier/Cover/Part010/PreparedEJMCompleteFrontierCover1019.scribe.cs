using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1019Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1019.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1019",
        H("Original frontier context coverage 1019"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48914", "selected_cut_48914", "Selected cut at depth 8, code 1580, node 1364555",
                "At remaining fuel 13 and original index 1364555, selection on the full partial prefix of depth 8 and code 1580 returns the complete row with depth 8, base-four code 1580, original node 1364555, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16777216. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48962", "selected_cut_48962", "Selected cut at depth 11, code 101216, node 1380832",
                "At remaining fuel 10 and original index 1380832, selection on the full partial prefix of depth 11 and code 101216 returns the complete row with depth 11, base-four code 101216, original node 1380832, kind 2, reserved field 0, 1097 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-101186-1378821", "unmarked_context_11_101186_1378821", "Unmarked parent at depth 11, code 101186",
                "The frontier Boolean is false at remaining fuel 10, original node 1378821, the whole prefixCache at depth 11 and code 101186, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-6325-1380798", "unmarked_context_9_6325_1380798", "Unmarked parent at depth 9, code 6325",
                "The frontier Boolean is false at remaining fuel 12, original node 1380798, the whole prefixCache at depth 9 and code 6325, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-101186-1378821", "node_context_11_101186_1378821", "Original split at fuel 10 and node 1378821",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 448748, 1378748, 1378820. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-6325-1380798", "node_context_9_6325_1380798", "Original split at fuel 12 and node 1380798",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1380335, 893098, 1380582, 1380797. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-8-1580-1364555", "context_8_1580_1364555", "Context at depth 8, code 1580, node 1364555",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 1580 and original node 1364555, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-101216-1380832", "context_11_101216_1380832", "Context at depth 11, code 101216, node 1380832",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 101216 and original node 1380832, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
