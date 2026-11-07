using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0030Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0030.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0030",
        H("Original frontier context coverage 0030"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01442", "selected_cut_01442", "Selected cut at depth 13, code 18533, node 52675",
                "At remaining fuel 8 and original index 52675, selection on the full partial prefix of depth 13 and code 18533 returns the complete row with depth 13, base-four code 18533, original node 52675, kind 2, reserved field 0, 2385 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01489", "selected_cut_01489", "Selected cut at depth 13, code 18580, node 54061",
                "At remaining fuel 8 and original index 54061, selection on the full partial prefix of depth 13 and code 18580 returns the complete row with depth 13, base-four code 18580, original node 54061, kind 2, reserved field 0, 1417 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4633-52713", "unmarked_context_12_4633_52713", "Unmarked parent at depth 12, code 4633",
                "The frontier Boolean is false at remaining fuel 9, original node 52713, the whole prefixCache at depth 12 and code 4633, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4644-54034", "unmarked_context_12_4644_54034", "Unmarked parent at depth 12, code 4644",
                "The frontier Boolean is false at remaining fuel 9, original node 54034, the whole prefixCache at depth 12 and code 4644, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4633-52713", "node_context_12_4633_52713", "Original split at fuel 9 and node 52713",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 52635, 52675, 52701, 52712. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4644-54034", "node_context_12_4644_54034", "Original split at fuel 9 and node 54034",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 53889, 53957, 54011, 54033. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-18533-52675", "context_13_18533_52675", "Context at depth 13, code 18533, node 52675",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18533 and original node 52675, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-18580-54061", "context_13_18580_54061", "Context at depth 13, code 18580, node 54061",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18580 and original node 54061, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
