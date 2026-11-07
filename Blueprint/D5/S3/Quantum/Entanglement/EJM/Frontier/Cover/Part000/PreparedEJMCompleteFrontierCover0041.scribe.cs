using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0041Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0041.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0041",
        H("Original frontier context coverage 0041"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01969", "selected_cut_01969", "Selected cut at depth 12, code 5392, node 1738",
                "At remaining fuel 9 and original index 1738, selection on the full partial prefix of depth 12 and code 5392 returns the complete row with depth 12, base-four code 5392, original node 1738, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02018", "selected_cut_02018", "Selected cut at depth 13, code 21674, node 67167",
                "At remaining fuel 8 and original index 67167, selection on the full partial prefix of depth 13 and code 21674 returns the complete row with depth 13, base-four code 21674, original node 67167, kind 2, reserved field 0, 1413 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5394-65867", "unmarked_context_12_5394_65867", "Unmarked parent at depth 12, code 5394",
                "The frontier Boolean is false at remaining fuel 9, original node 65867, the whole prefixCache at depth 12 and code 5394, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1353-67092", "unmarked_context_11_1353_67092", "Unmarked parent at depth 11, code 1353",
                "The frontier Boolean is false at remaining fuel 10, original node 67092, the whole prefixCache at depth 11 and code 1353, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5394-65867", "node_context_12_5394_65867", "Original split at fuel 9 and node 65867",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 65795, 65827, 65852, 65866. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1353-67092", "node_context_11_1353_67092", "Original split at fuel 10 and node 67092",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 1738, 66988, 67091. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-5392-1738", "context_12_5392_1738", "Context at depth 12, code 5392, node 1738",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5392 and original node 1738, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-21674-67167", "context_13_21674_67167", "Context at depth 13, code 21674, node 67167",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 21674 and original node 67167, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
