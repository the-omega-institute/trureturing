using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0799Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0799.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0799",
        H("Original frontier context coverage 0799"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38355", "selected_cut_38355", "Selected cut at depth 12, code 301332, node 1033365",
                "At remaining fuel 9 and original index 1033365, selection on the full partial prefix of depth 12 and code 301332 returns the complete row with depth 12, base-four code 301332, original node 1033365, kind 2, reserved field 0, 2489 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38402", "selected_cut_38402", "Selected cut at depth 12, code 301382, node 1035077",
                "At remaining fuel 9 and original index 1035077, selection on the full partial prefix of depth 12 and code 301382 returns the complete row with depth 12, base-four code 301382, original node 1035077, kind 2, reserved field 0, 2277 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75332-1033319", "unmarked_context_11_75332_1033319", "Unmarked parent at depth 11, code 75332",
                "The frontier Boolean is false at remaining fuel 10, original node 1033319, the whole prefixCache at depth 11 and code 75332, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75344-1034969", "unmarked_context_11_75344_1034969", "Unmarked parent at depth 11, code 75344",
                "The frontier Boolean is false at remaining fuel 10, original node 1034969, the whole prefixCache at depth 11 and code 75344, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75332-1033319", "node_context_11_75332_1033319", "Original split at fuel 10 and node 1033319",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1033191, 1033241, 1033279, 1033318. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75344-1034969", "node_context_11_75344_1034969", "Original split at fuel 10 and node 1034969",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1034854, 1034898, 1034934, 1034968. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-75332-1033319", "context_11_75332_1033319", "Context at depth 11, code 75332, node 1033319",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75332 and original node 1033319, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_301328_1033191, context_12_301329_1033241, context_12_301330_1033279, context_12_301331_1033318.", DescribeRole.Theorem),
            Node("context-12-301382-1035077", "context_12_301382_1035077", "Context at depth 12, code 301382, node 1035077",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301382 and original node 1035077, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
