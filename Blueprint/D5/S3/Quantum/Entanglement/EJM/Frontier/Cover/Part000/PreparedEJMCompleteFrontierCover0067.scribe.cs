using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0067Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0067.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0067",
        H("Original frontier context coverage 0067"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03219", "selected_cut_03219", "Selected cut at depth 12, code 6798, node 100945",
                "At remaining fuel 9 and original index 100945, selection on the full partial prefix of depth 12 and code 6798 returns the complete row with depth 12, base-four code 6798, original node 100945, kind 2, reserved field 0, 2501 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03265", "selected_cut_03265", "Selected cut at depth 14, code 110611, node 102989",
                "At remaining fuel 7 and original index 102989, selection on the full partial prefix of depth 14 and code 110611 returns the complete row with depth 14, base-four code 110611, original node 102989, kind 2, reserved field 0, 1209 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-1699-100990", "unmarked_context_11_1699_100990", "Unmarked parent at depth 11, code 1699",
                "The frontier Boolean is false at remaining fuel 10, original node 100990, the whole prefixCache at depth 11 and code 1699, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-27652-102990", "unmarked_context_13_27652_102990", "Unmarked parent at depth 13, code 27652",
                "The frontier Boolean is false at remaining fuel 8, original node 102990, the whole prefixCache at depth 13 and code 27652, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-1699-100990", "node_context_11_1699_100990", "Original split at fuel 10 and node 100990",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 100838, 100894, 100945, 100989. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-27652-102990", "node_context_13_27652_102990", "Original split at fuel 8 and node 102990",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 102908, 102940, 102965, 102989. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-6798-100945", "context_12_6798_100945", "Context at depth 12, code 6798, node 100945",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 6798 and original node 100945, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-27652-102990", "context_13_27652_102990", "Context at depth 13, code 27652, node 102990",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 27652 and original node 102990, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_110608_102908, context_14_110609_102940, context_14_110610_102965, context_14_110611_102989.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
