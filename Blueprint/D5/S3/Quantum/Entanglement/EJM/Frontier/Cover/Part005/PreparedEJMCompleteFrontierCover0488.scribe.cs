using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0488Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0488.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0488",
        H("Original frontier context coverage 0488"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23428", "selected_cut_23428", "Selected cut at depth 12, code 76384, node 593285",
                "At remaining fuel 9 and original index 593285, selection on the full partial prefix of depth 12 and code 76384 returns the complete row with depth 12, base-four code 76384, original node 593285, kind 2, reserved field 0, 3173 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23474", "selected_cut_23474", "Selected cut at depth 12, code 76427, node 594596",
                "At remaining fuel 9 and original index 594596, selection on the full partial prefix of depth 12 and code 76427 returns the complete row with depth 12, base-four code 76427, original node 594596, kind 2, reserved field 0, 1361 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19095-593243", "unmarked_context_11_19095_593243", "Unmarked parent at depth 11, code 19095",
                "The frontier Boolean is false at remaining fuel 10, original node 593243, the whole prefixCache at depth 11 and code 19095, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19106-594597", "unmarked_context_11_19106_594597", "Unmarked parent at depth 11, code 19106",
                "The frontier Boolean is false at remaining fuel 10, original node 594597, the whole prefixCache at depth 11 and code 19106, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19095-593243", "node_context_11_19095_593243", "Original split at fuel 10 and node 593243",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 593082, 593130, 593186, 593242. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19106-594597", "node_context_11_19106_594597", "Original split at fuel 10 and node 594597",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 594556, 594579, 188189, 594596. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-19095-593243", "context_11_19095_593243", "Context at depth 11, code 19095, node 593243",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19095 and original node 593243, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_76380_593082, context_12_76381_593130, context_12_76382_593186, context_12_76383_593242.", DescribeRole.Theorem),
            Node("context-11-19106-594597", "context_11_19106_594597", "Context at depth 11, code 19106, node 594597",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19106 and original node 594597, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_76424_594556, context_12_76425_594579, context_12_76426_188189, context_12_76427_594596.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
