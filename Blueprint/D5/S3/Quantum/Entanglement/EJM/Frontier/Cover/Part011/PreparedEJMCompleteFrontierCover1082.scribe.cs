using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1082Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1082.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1082",
        H("Original frontier context coverage 1082"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51938", "selected_cut_51938", "Selected cut at depth 10, code 71360, node 1468246",
                "At remaining fuel 11 and original index 1468246, selection on the full partial prefix of depth 10 and code 71360 returns the complete row with depth 10, base-four code 71360, original node 1468246, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51986", "selected_cut_51986", "Selected cut at depth 11, code 285572, node 1505455",
                "At remaining fuel 10 and original index 1505455, selection on the full partial prefix of depth 11 and code 285572 returns the complete row with depth 11, base-four code 285572, original node 1505455, kind 2, reserved field 0, 3277 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-71361-1503814", "unmarked_context_10_71361_1503814", "Unmarked parent at depth 10, code 71361",
                "The frontier Boolean is false at remaining fuel 11, original node 1503814, the whole prefixCache at depth 10 and code 71361, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-4461-1505357", "unmarked_context_8_4461_1505357", "Unmarked parent at depth 8, code 4461",
                "The frontier Boolean is false at remaining fuel 13, original node 1505357, the whole prefixCache at depth 8 and code 4461, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-71361-1503814", "node_context_10_71361_1503814", "Original split at fuel 11 and node 1503814",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1503698, 1468419, 1503788, 1503813. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-4461-1505357", "node_context_8_4461_1505357", "Original split at fuel 13 and node 1505357",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1504939, 1505172, 1505301, 1505356. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-71360-1468246", "context_10_71360_1468246", "Context at depth 10, code 71360, node 1468246",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 71360 and original node 1468246, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-285572-1505455", "context_11_285572_1505455", "Context at depth 11, code 285572, node 1505455",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 285572 and original node 1505455, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
