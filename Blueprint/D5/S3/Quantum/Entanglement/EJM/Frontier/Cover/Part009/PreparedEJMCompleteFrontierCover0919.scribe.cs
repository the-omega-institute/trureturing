using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0919Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0919.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0919",
        H("Original frontier context coverage 0919"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44115", "selected_cut_44115", "Selected cut at depth 12, code 353310, node 1211314",
                "At remaining fuel 9 and original index 1211314, selection on the full partial prefix of depth 12 and code 353310 returns the complete row with depth 12, base-four code 353310, original node 1211314, kind 2, reserved field 0, 2845 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44161", "selected_cut_44161", "Selected cut at depth 12, code 353359, node 1212697",
                "At remaining fuel 9 and original index 1212697, selection on the full partial prefix of depth 12 and code 353359 returns the complete row with depth 12, base-four code 353359, original node 1212697, kind 2, reserved field 0, 1829 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88327-1211361", "unmarked_context_11_88327_1211361", "Unmarked parent at depth 11, code 88327",
                "The frontier Boolean is false at remaining fuel 10, original node 1211361, the whole prefixCache at depth 11 and code 88327, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-22084-1212699", "unmarked_context_10_22084_1212699", "Unmarked parent at depth 10, code 22084",
                "The frontier Boolean is false at remaining fuel 11, original node 1212699, the whole prefixCache at depth 10 and code 22084, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88327-1211361", "node_context_11_88327_1211361", "Original split at fuel 10 and node 1211361",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 539296, 1211258, 1211314, 1211360. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-22084-1212699", "node_context_10_22084_1212699", "Original split at fuel 11 and node 1212699",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1212427, 1212496, 1212609, 1212698. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-353310-1211314", "context_12_353310_1211314", "Context at depth 12, code 353310, node 1211314",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 353310 and original node 1211314, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-22084-1212699", "context_10_22084_1212699", "Context at depth 10, code 22084, node 1212699",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22084 and original node 1212699, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_88336_1212427, context_11_88337_1212496, context_11_88338_1212609, context_11_88339_1212698.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
