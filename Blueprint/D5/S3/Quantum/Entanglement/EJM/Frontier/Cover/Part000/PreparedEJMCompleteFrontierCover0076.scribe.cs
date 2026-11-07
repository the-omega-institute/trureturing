using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0076Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0076.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0076",
        H("Original frontier context coverage 0076"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03651", "selected_cut_03651", "Selected cut at depth 12, code 7050, node 113637",
                "At remaining fuel 9 and original index 113637, selection on the full partial prefix of depth 12 and code 7050 returns the complete row with depth 12, base-four code 7050, original node 113637, kind 2, reserved field 0, 2693 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03696", "selected_cut_03696", "Selected cut at depth 9, code 111, node 116309",
                "At remaining fuel 12 and original index 116309, selection on the full partial prefix of depth 9 and code 111 returns the complete row with depth 9, base-four code 111, original node 116309, kind 1, reserved field 0, 1 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-1762-113686", "unmarked_context_11_1762_113686", "Unmarked parent at depth 11, code 1762",
                "The frontier Boolean is false at remaining fuel 10, original node 113686, the whole prefixCache at depth 11 and code 1762, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-7-6-116311", "unmarked_context_7_6_116311", "Unmarked parent at depth 7, code 6",
                "The frontier Boolean is false at remaining fuel 14, original node 116311, the whole prefixCache at depth 7 and code 6, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-1762-113686", "node_context_11_1762_113686", "Original split at fuel 10 and node 113686",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 113535, 113590, 113637, 113685. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-7-6-116311", "node_context_7_6_116311", "Original split at fuel 14 and node 116311",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 14300, 14300, 102866, 116310. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-7050-113637", "context_12_7050_113637", "Context at depth 12, code 7050, node 113637",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 7050 and original node 113637, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-7-6-116311", "context_7_6_116311", "Context at depth 7, code 6, node 116311",
                "The conclusion is adaptive Accepted at the exact depth 7, full base-four code 6 and original node 116311, hence remaining fuel 14, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_8_24_14300, context_8_25_14300, context_8_26_102866, context_8_27_116310.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
