using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0028Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0028.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0028",
        H("Original frontier context coverage 0028"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01346", "selected_cut_01346", "Selected cut at depth 13, code 18452, node 49663",
                "At remaining fuel 8 and original index 49663, selection on the full partial prefix of depth 13 and code 18452 returns the complete row with depth 13, base-four code 18452, original node 49663, kind 2, reserved field 0, 3889 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01393", "selected_cut_01393", "Selected cut at depth 13, code 18484, node 51198",
                "At remaining fuel 8 and original index 51198, selection on the full partial prefix of depth 13 and code 18484 returns the complete row with depth 13, base-four code 18484, original node 51198, kind 2, reserved field 0, 3273 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4612-49588", "unmarked_context_12_4612_49588", "Unmarked parent at depth 12, code 4612",
                "The frontier Boolean is false at remaining fuel 9, original node 49588, the whole prefixCache at depth 12 and code 4612, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4620-51130", "unmarked_context_12_4620_51130", "Unmarked parent at depth 12, code 4620",
                "The frontier Boolean is false at remaining fuel 9, original node 51130, the whole prefixCache at depth 12 and code 4620, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4612-49588", "node_context_12_4612_49588", "Original split at fuel 9 and node 49588",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 49344, 49471, 49556, 49587. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4620-51130", "node_context_12_4620_51130", "Original split at fuel 9 and node 51130",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 50923, 51071, 51128, 51129. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-4612-49588", "context_12_4612_49588", "Context at depth 12, code 4612, node 49588",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4612 and original node 49588, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_18448_49344, context_13_18449_49471, context_13_18450_49556, context_13_18451_49587.", DescribeRole.Theorem),
            Node("context-13-18484-51198", "context_13_18484_51198", "Context at depth 13, code 18484, node 51198",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18484 and original node 51198, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
