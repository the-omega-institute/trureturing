using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0332Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0332.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0332",
        H("Original frontier context coverage 0332"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15940", "selected_cut_15940", "Selected cut at depth 12, code 27988, node 406803",
                "At remaining fuel 9 and original index 406803, selection on the full partial prefix of depth 12 and code 27988 returns the complete row with depth 12, base-four code 27988, original node 406803, kind 2, reserved field 0, 3633 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15987", "selected_cut_15987", "Selected cut at depth 13, code 112014, node 407517",
                "At remaining fuel 8 and original index 407517, selection on the full partial prefix of depth 13 and code 112014 returns the complete row with depth 13, base-four code 112014, original node 407517, kind 2, reserved field 0, 2633 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27987-406758", "unmarked_context_12_27987_406758", "Unmarked parent at depth 12, code 27987",
                "The frontier Boolean is false at remaining fuel 9, original node 406758, the whole prefixCache at depth 12 and code 27987, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-28002-407447", "unmarked_context_12_28002_407447", "Unmarked parent at depth 12, code 28002",
                "The frontier Boolean is false at remaining fuel 9, original node 407447, the whole prefixCache at depth 12 and code 28002, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27987-406758", "node_context_12_27987_406758", "Original split at fuel 9 and node 406758",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 406710, 406748, 406757. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-28002-407447", "node_context_12_28002_407447", "Original split at fuel 9 and node 407447",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 407403, 407433, 407446. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-27987-406758", "context_12_27987_406758", "Context at depth 12, code 27987, node 406758",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27987 and original node 406758, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_111948_3444, context_13_111949_406710, context_13_111950_406748, context_13_111951_406757.", DescribeRole.Theorem),
            Node("context-13-112014-407517", "context_13_112014_407517", "Context at depth 13, code 112014, node 407517",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112014 and original node 407517, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
