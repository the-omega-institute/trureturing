using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1083Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1083.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1083",
        H("Original frontier context coverage 1083"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51987", "selected_cut_51987", "Selected cut at depth 11, code 285573, node 1468419",
                "At remaining fuel 10 and original index 1468419, selection on the full partial prefix of depth 11 and code 285573 returns the complete row with depth 11, base-four code 285573, original node 1468419, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52032", "selected_cut_52032", "Selected cut at depth 6, code 279, node 116314",
                "At remaining fuel 15 and original index 116314, selection on the full partial prefix of depth 6 and code 279 returns the complete row with depth 6, base-four code 279, original node 116314, kind 1, reserved field 0, 1 subtree occurrences and completion domain 268435456. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-71393-1505578", "unmarked_context_10_71393_1505578", "Unmarked parent at depth 10, code 71393",
                "The frontier Boolean is false at remaining fuel 11, original node 1505578, the whole prefixCache at depth 10 and code 71393, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-5-69-1507378", "unmarked_context_5_69_1507378", "Unmarked parent at depth 5, code 69",
                "The frontier Boolean is false at remaining fuel 16, original node 1507378, the whole prefixCache at depth 5 and code 69, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-71393-1505578", "node_context_10_71393_1505578", "Original split at fuel 11 and node 1505578",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1505455, 1468419, 1505546, 1505577. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-5-69-1507378", "node_context_5_69_1507378", "Original split at fuel 16 and node 1507378",
                "The complete original decoder output is the split at coordinate 5, with value children 0 through 3 respectively at original indices 1492908, 1475984, 1507377, 116314. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-285573-1468419", "context_11_285573_1468419", "Context at depth 11, code 285573, node 1468419",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 285573 and original node 1468419, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-5-69-1507378", "context_5_69_1507378", "Context at depth 5, code 69, node 1507378",
                "The conclusion is adaptive Accepted at the exact depth 5, full base-four code 69 and original node 1507378, hence remaining fuel 16, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_6_276_1492908, context_6_277_1475984, context_6_278_1507377, context_6_279_116314.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
