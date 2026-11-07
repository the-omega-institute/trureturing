using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0123Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0123.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0123",
        H("Original frontier context coverage 0123"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05906", "selected_cut_05906", "Selected cut at depth 13, code 84053, node 180587",
                "At remaining fuel 8 and original index 180587, selection on the full partial prefix of depth 13 and code 84053 returns the complete row with depth 13, base-four code 84053, original node 180587, kind 2, reserved field 0, 1833 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05953", "selected_cut_05953", "Selected cut at depth 13, code 84103, node 181679",
                "At remaining fuel 8 and original index 181679, selection on the full partial prefix of depth 13 and code 84103 returns the complete row with depth 13, base-four code 84103, original node 181679, kind 2, reserved field 0, 677 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-21013-180613", "unmarked_context_12_21013_180613", "Unmarked parent at depth 12, code 21013",
                "The frontier Boolean is false at remaining fuel 9, original node 180613, the whole prefixCache at depth 12 and code 21013, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21025-181680", "unmarked_context_12_21025_181680", "Unmarked parent at depth 12, code 21025",
                "The frontier Boolean is false at remaining fuel 9, original node 181680, the whole prefixCache at depth 12 and code 21025, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-21013-180613", "node_context_12_21013_180613", "Original split at fuel 9 and node 180613",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 180561, 180587, 180605, 180612. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21025-181680", "node_context_12_21025_181680", "Original split at fuel 9 and node 181680",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 181627, 181653, 181672, 181679. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-84053-180587", "context_13_84053_180587", "Context at depth 13, code 84053, node 180587",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 84053 and original node 180587, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-21025-181680", "context_12_21025_181680", "Context at depth 12, code 21025, node 181680",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21025 and original node 181680, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_84100_181627, context_13_84101_181653, context_13_84102_181672, context_13_84103_181679.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
