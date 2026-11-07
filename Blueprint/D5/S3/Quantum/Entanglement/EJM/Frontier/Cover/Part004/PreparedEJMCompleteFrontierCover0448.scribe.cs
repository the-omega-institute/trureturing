using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0448Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0448.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0448",
        H("Original frontier context coverage 0448"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21507", "selected_cut_21507", "Selected cut at depth 13, code 300261, node 550366",
                "At remaining fuel 8 and original index 550366, selection on the full partial prefix of depth 13 and code 300261 returns the complete row with depth 13, base-four code 300261, original node 550366, kind 2, reserved field 0, 2057 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21554", "selected_cut_21554", "Selected cut at depth 13, code 300335, node 551335",
                "At remaining fuel 8 and original index 551335, selection on the full partial prefix of depth 13 and code 300335 returns the complete row with depth 13, base-four code 300335, original node 551335, kind 2, reserved field 0, 937 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75065-550394", "unmarked_context_12_75065_550394", "Unmarked parent at depth 12, code 75065",
                "The frontier Boolean is false at remaining fuel 9, original node 550394, the whole prefixCache at depth 12 and code 75065, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75083-551336", "unmarked_context_12_75083_551336", "Unmarked parent at depth 12, code 75083",
                "The frontier Boolean is false at remaining fuel 9, original node 551336, the whole prefixCache at depth 12 and code 75083, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75065-550394", "node_context_12_75065_550394", "Original split at fuel 9 and node 550394",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 550341, 550366, 550385, 550393. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75083-551336", "node_context_12_75083_551336", "Original split at fuel 9 and node 551336",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 551287, 551325, 551335. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-300261-550366", "context_13_300261_550366", "Context at depth 13, code 300261, node 550366",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 300261 and original node 550366, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-75083-551336", "context_12_75083_551336", "Context at depth 12, code 75083, node 551336",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75083 and original node 551336, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_300332_3444, context_13_300333_551287, context_13_300334_551325, context_13_300335_551335.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
