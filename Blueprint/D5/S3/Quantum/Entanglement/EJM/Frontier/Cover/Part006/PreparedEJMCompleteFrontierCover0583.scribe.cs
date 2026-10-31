using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0583Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0583.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0583",
        H("Original frontier context coverage 0583"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27987", "selected_cut_27987", "Selected cut at depth 13, code 367881, node 706514",
                "At remaining fuel 8 and original index 706514, selection on the full partial prefix of depth 13 and code 367881 returns the complete row with depth 13, base-four code 367881, original node 706514, kind 2, reserved field 0, 2501 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28034", "selected_cut_28034", "Selected cut at depth 12, code 92003, node 707859",
                "At remaining fuel 9 and original index 707859, selection on the full partial prefix of depth 12 and code 92003 returns the complete row with depth 12, base-four code 92003, original node 707859, kind 2, reserved field 0, 2845 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91970-706540", "unmarked_context_12_91970_706540", "Unmarked parent at depth 12, code 91970",
                "The frontier Boolean is false at remaining fuel 9, original node 706540, the whole prefixCache at depth 12 and code 91970, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23000-707860", "unmarked_context_11_23000_707860", "Unmarked parent at depth 11, code 23000",
                "The frontier Boolean is false at remaining fuel 10, original node 707860, the whole prefixCache at depth 11 and code 23000, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91970-706540", "node_context_12_91970_706540", "Original split at fuel 9 and node 706540",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 706514, 706535, 706539. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23000-707860", "node_context_11_23000_707860", "Original split at fuel 10 and node 707860",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 707691, 707776, 707821, 707859. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-367881-706514", "context_13_367881_706514", "Context at depth 13, code 367881, node 706514",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 367881 and original node 706514, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-23000-707860", "context_11_23000_707860", "Context at depth 11, code 23000, node 707860",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 23000 and original node 707860, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_92000_707691, context_12_92001_707776, context_12_92002_707821, context_12_92003_707859.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
