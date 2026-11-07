using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0966Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0966.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0966",
        H("Original frontier context coverage 0966"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46371", "selected_cut_46371", "Selected cut at depth 12, code 370500, node 1292976",
                "At remaining fuel 9 and original index 1292976, selection on the full partial prefix of depth 12 and code 370500 returns the complete row with depth 12, base-four code 370500, original node 1292976, kind 2, reserved field 0, 2045 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46417", "selected_cut_46417", "Selected cut at depth 10, code 23167, node 1294175",
                "At remaining fuel 11 and original index 1294175, selection on the full partial prefix of depth 10 and code 23167 returns the complete row with depth 10, base-four code 23167, original node 1294175, kind 2, reserved field 0, 121 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92625-1293069", "unmarked_context_11_92625_1293069", "Unmarked parent at depth 11, code 92625",
                "The frontier Boolean is false at remaining fuel 10, original node 1293069, the whole prefixCache at depth 11 and code 92625, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-7-361-1294178", "unmarked_context_7_361_1294178", "Unmarked parent at depth 7, code 361",
                "The frontier Boolean is false at remaining fuel 14, original node 1294178, the whole prefixCache at depth 7 and code 361, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92625-1293069", "node_context_11_92625_1293069", "Original split at fuel 10 and node 1293069",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1292976, 1257136, 1293014, 1293068. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-7-361-1294178", "node_context_7_361_1294178", "Original split at fuel 14 and node 1294178",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 1284682, 1287593, 1291003, 1294177. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-370500-1292976", "context_12_370500_1292976", "Context at depth 12, code 370500, node 1292976",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 370500 and original node 1292976, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-7-361-1294178", "context_7_361_1294178", "Context at depth 7, code 361, node 1294178",
                "The conclusion is adaptive Accepted at the exact depth 7, full base-four code 361 and original node 1294178, hence remaining fuel 14, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_8_1444_1284682, context_8_1445_1287593, context_8_1446_1291003, context_8_1447_1294177.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
