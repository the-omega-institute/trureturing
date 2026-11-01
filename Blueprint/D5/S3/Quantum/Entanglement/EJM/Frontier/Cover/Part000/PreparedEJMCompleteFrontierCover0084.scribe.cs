using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0084Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0084.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0084",
        H("Original frontier context coverage 0084"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04034", "selected_cut_04034", "Selected cut at depth 13, code 71720, node 128649",
                "At remaining fuel 8 and original index 128649, selection on the full partial prefix of depth 13 and code 71720 returns the complete row with depth 13, base-four code 71720, original node 128649, kind 2, reserved field 0, 3913 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04081", "selected_cut_04081", "Selected cut at depth 13, code 71776, node 129970",
                "At remaining fuel 8 and original index 129970, selection on the full partial prefix of depth 13 and code 71776 returns the complete row with depth 13, base-four code 71776, original node 129970, kind 2, reserved field 0, 1309 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-17930-128743", "unmarked_context_12_17930_128743", "Unmarked parent at depth 12, code 17930",
                "The frontier Boolean is false at remaining fuel 9, original node 128743, the whole prefixCache at depth 12 and code 17930, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4485-129950", "unmarked_context_11_4485_129950", "Unmarked parent at depth 11, code 4485",
                "The frontier Boolean is false at remaining fuel 10, original node 129950, the whole prefixCache at depth 11 and code 4485, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-17930-128743", "node_context_12_17930_128743", "Original split at fuel 9 and node 128743",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 128649, 128716, 128740, 128742. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4485-129950", "node_context_11_4485_129950", "Original split at fuel 10 and node 129950",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 129488, 129633, 129781, 129949. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-71720-128649", "context_13_71720_128649", "Context at depth 13, code 71720, node 128649",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 71720 and original node 128649, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-71776-129970", "context_13_71776_129970", "Context at depth 13, code 71776, node 129970",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 71776 and original node 129970, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
