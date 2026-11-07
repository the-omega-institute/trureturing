using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0978Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0978.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0978",
        H("Original frontier context coverage 0978"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46948", "selected_cut_46948", "Selected cut at depth 12, code 371992, node 1055595",
                "At remaining fuel 9 and original index 1055595, selection on the full partial prefix of depth 12 and code 371992 returns the complete row with depth 12, base-four code 371992, original node 1055595, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46994", "selected_cut_46994", "Selected cut at depth 12, code 372047, node 1313115",
                "At remaining fuel 9 and original index 1313115, selection on the full partial prefix of depth 12 and code 372047 returns the complete row with depth 12, base-four code 372047, original node 1313115, kind 2, reserved field 0, 1437 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92997-1311701", "unmarked_context_11_92997_1311701", "Unmarked parent at depth 11, code 92997",
                "The frontier Boolean is false at remaining fuel 10, original node 1311701, the whole prefixCache at depth 11 and code 92997, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23252-1313117", "unmarked_context_10_23252_1313117", "Unmarked parent at depth 10, code 23252",
                "The frontier Boolean is false at remaining fuel 11, original node 1313117, the whole prefixCache at depth 10 and code 23252, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92997-1311701", "node_context_11_92997_1311701", "Original split at fuel 10 and node 1311701",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1311657, 1172003, 1311700, 692794. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23252-1313117", "node_context_10_23252_1313117", "Original split at fuel 11 and node 1313117",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1312877, 1312973, 1313031, 1313116. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-92997-1311701", "context_11_92997_1311701", "Context at depth 11, code 92997, node 1311701",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92997 and original node 1311701, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_371988_1311657, context_12_371989_1172003, context_12_371990_1311700, context_12_371991_692794.", DescribeRole.Theorem),
            Node("context-10-23252-1313117", "context_10_23252_1313117", "Context at depth 10, code 23252, node 1313117",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23252 and original node 1313117, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_93008_1312877, context_11_93009_1312973, context_11_93010_1313031, context_11_93011_1313116.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
