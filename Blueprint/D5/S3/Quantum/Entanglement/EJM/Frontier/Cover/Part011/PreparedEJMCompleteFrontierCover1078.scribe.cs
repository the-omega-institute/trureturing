using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1078Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1078.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1078",
        H("Original frontier context coverage 1078"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51747", "selected_cut_51747", "Selected cut at depth 11, code 284826, node 1468743",
                "At remaining fuel 10 and original index 1468743, selection on the full partial prefix of depth 11 and code 284826 returns the complete row with depth 11, base-four code 284826, original node 1468743, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51794", "selected_cut_51794", "Selected cut at depth 11, code 284942, node 1497592",
                "At remaining fuel 10 and original index 1497592, selection on the full partial prefix of depth 11 and code 284942 returns the complete row with depth 11, base-four code 284942, original node 1497592, kind 2, reserved field 0, 2141 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-71206-1495707", "unmarked_context_10_71206_1495707", "Unmarked parent at depth 10, code 71206",
                "The frontier Boolean is false at remaining fuel 11, original node 1495707, the whole prefixCache at depth 10 and code 71206, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-71234-1497474", "unmarked_context_10_71234_1497474", "Unmarked parent at depth 10, code 71234",
                "The frontier Boolean is false at remaining fuel 11, original node 1497474, the whole prefixCache at depth 10 and code 71234, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-71206-1495707", "node_context_10_71206_1495707", "Original split at fuel 11 and node 1495707",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1495655, 1495682, 1468743, 1495706. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-71234-1497474", "node_context_10_71234_1497474", "Original split at fuel 11 and node 1497474",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1497389, 1497427, 1468743, 1497473. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-284826-1468743", "context_11_284826_1468743", "Context at depth 11, code 284826, node 1468743",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 284826 and original node 1468743, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-284942-1497592", "context_11_284942_1497592", "Context at depth 11, code 284942, node 1497592",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 284942 and original node 1497592, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
