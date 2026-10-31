using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0027Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0027.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0027",
        H("Original frontier context coverage 0027"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01298", "selected_cut_01298", "Selected cut at depth 12, code 4502, node 47761",
                "At remaining fuel 9 and original index 47761, selection on the full partial prefix of depth 12 and code 4502 returns the complete row with depth 12, base-four code 4502, original node 47761, kind 2, reserved field 0, 1745 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01345", "selected_cut_01345", "Selected cut at depth 13, code 18451, node 49587",
                "At remaining fuel 8 and original index 49587, selection on the full partial prefix of depth 13 and code 18451 returns the complete row with depth 13, base-four code 18451, original node 49587, kind 2, reserved field 0, 1493 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-1125-47789", "unmarked_context_11_1125_47789", "Unmarked parent at depth 11, code 1125",
                "The frontier Boolean is false at remaining fuel 10, original node 47789, the whole prefixCache at depth 11 and code 1125, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-18449-49471", "unmarked_context_13_18449_49471", "Unmarked parent at depth 13, code 18449",
                "The frontier Boolean is false at remaining fuel 8, original node 49471, the whole prefixCache at depth 13 and code 18449, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-1125-47789", "node_context_11_1125_47789", "Original split at fuel 10 and node 47789",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 47649, 47729, 47761, 47788. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-18449-49471", "node_context_13_18449_49471", "Original split at fuel 8 and node 49471",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 49388, 49416, 49445, 49470. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-4502-47761", "context_12_4502_47761", "Context at depth 12, code 4502, node 47761",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4502 and original node 47761, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-18451-49587", "context_13_18451_49587", "Context at depth 13, code 18451, node 49587",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18451 and original node 49587, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
