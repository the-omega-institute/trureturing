using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1001Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1001.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1001",
        H("Original frontier context coverage 1001"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48052", "selected_cut_48052", "Selected cut at depth 12, code 375088, node 1255011",
                "At remaining fuel 9 and original index 1255011, selection on the full partial prefix of depth 12 and code 375088 returns the complete row with depth 12, base-four code 375088, original node 1255011, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48099", "selected_cut_48099", "Selected cut at depth 10, code 23454, node 1347931",
                "At remaining fuel 11 and original index 1347931, selection on the full partial prefix of depth 10 and code 23454 returns the complete row with depth 10, base-four code 23454, original node 1347931, kind 2, reserved field 0, 1069 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23442-1346302", "unmarked_context_10_23442_1346302", "Unmarked parent at depth 10, code 23442",
                "The frontier Boolean is false at remaining fuel 11, original node 1346302, the whole prefixCache at depth 10 and code 23442, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23452-1347837", "unmarked_context_10_23452_1347837", "Unmarked parent at depth 10, code 23452",
                "The frontier Boolean is false at remaining fuel 11, original node 1347837, the whole prefixCache at depth 10 and code 23452, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23442-1346302", "node_context_10_23442_1346302", "Original split at fuel 11 and node 1346302",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1346103, 1346174, 900587, 1346301. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23452-1347837", "node_context_10_23452_1347837", "Original split at fuel 11 and node 1347837",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1347742, 1347771, 1347797, 1347836. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23442-1346302", "context_10_23442_1346302", "Context at depth 10, code 23442, node 1346302",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23442 and original node 1346302, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_93768_1346103, context_11_93769_1346174, context_11_93770_900587, context_11_93771_1346301.", DescribeRole.Theorem),
            Node("context-10-23454-1347931", "context_10_23454_1347931", "Context at depth 10, code 23454, node 1347931",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23454 and original node 1347931, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
