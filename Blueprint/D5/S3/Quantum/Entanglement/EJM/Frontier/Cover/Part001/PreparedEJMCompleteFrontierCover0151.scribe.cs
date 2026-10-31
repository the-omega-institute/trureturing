using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0151Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0151.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0151",
        H("Original frontier context coverage 0151"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07250", "selected_cut_07250", "Selected cut at depth 12, code 22148, node 211150",
                "At remaining fuel 9 and original index 211150, selection on the full partial prefix of depth 12 and code 22148 returns the complete row with depth 12, base-four code 22148, original node 211150, kind 2, reserved field 0, 2429 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07298", "selected_cut_07298", "Selected cut at depth 12, code 22199, node 212294",
                "At remaining fuel 9 and original index 212294, selection on the full partial prefix of depth 12 and code 22199 returns the complete row with depth 12, base-four code 22199, original node 212294, kind 2, reserved field 0, 1101 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5537-211237", "unmarked_context_11_5537_211237", "Unmarked parent at depth 11, code 5537",
                "The frontier Boolean is false at remaining fuel 10, original node 211237, the whole prefixCache at depth 11 and code 5537, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5549-212295", "unmarked_context_11_5549_212295", "Unmarked parent at depth 11, code 5549",
                "The frontier Boolean is false at remaining fuel 10, original node 212295, the whole prefixCache at depth 11 and code 5549, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5537-211237", "node_context_11_5537_211237", "Original split at fuel 10 and node 211237",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 211150, 211179, 211208, 211236. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5549-212295", "node_context_11_5549_212295", "Original split at fuel 10 and node 212295",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 212256, 212269, 212283, 212294. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-22148-211150", "context_12_22148_211150", "Context at depth 12, code 22148, node 211150",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22148 and original node 211150, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-5549-212295", "context_11_5549_212295", "Context at depth 11, code 5549, node 212295",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5549 and original node 212295, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_22196_212256, context_12_22197_212269, context_12_22198_212283, context_12_22199_212294.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
