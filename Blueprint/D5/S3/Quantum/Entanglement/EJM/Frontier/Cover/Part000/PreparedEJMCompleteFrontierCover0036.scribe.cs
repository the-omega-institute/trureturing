using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0036Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0036.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0036",
        H("Original frontier context coverage 0036"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01731", "selected_cut_01731", "Selected cut at depth 13, code 18810, node 59287",
                "At remaining fuel 8 and original index 59287, selection on the full partial prefix of depth 13 and code 18810 returns the complete row with depth 13, base-four code 18810, original node 59287, kind 2, reserved field 0, 2497 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01778", "selected_cut_01778", "Selected cut at depth 13, code 18863, node 60164",
                "At remaining fuel 8 and original index 60164, selection on the full partial prefix of depth 13 and code 18863 returns the complete row with depth 13, base-four code 18863, original node 60164, kind 2, reserved field 0, 1113 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4702-59312", "unmarked_context_12_4702_59312", "Unmarked parent at depth 12, code 4702",
                "The frontier Boolean is false at remaining fuel 9, original node 59312, the whole prefixCache at depth 12 and code 4702, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4715-60165", "unmarked_context_12_4715_60165", "Unmarked parent at depth 12, code 4715",
                "The frontier Boolean is false at remaining fuel 9, original node 60165, the whole prefixCache at depth 12 and code 4715, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4702-59312", "node_context_12_4702_59312", "Original split at fuel 9 and node 59312",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 59248, 59287, 59311. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4715-60165", "node_context_12_4715_60165", "Original split at fuel 9 and node 60165",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 60136, 60157, 60164. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-18810-59287", "context_13_18810_59287", "Context at depth 13, code 18810, node 59287",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18810 and original node 59287, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-4715-60165", "context_12_4715_60165", "Context at depth 12, code 4715, node 60165",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4715 and original node 60165, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_18860_3444, context_13_18861_60136, context_13_18862_60157, context_13_18863_60164.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
