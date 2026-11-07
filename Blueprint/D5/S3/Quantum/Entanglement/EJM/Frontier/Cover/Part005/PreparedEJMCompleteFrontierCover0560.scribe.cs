using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0560Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0560.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0560",
        H("Original frontier context coverage 0560"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26883", "selected_cut_26883", "Selected cut at depth 13, code 364686, node 679954",
                "At remaining fuel 8 and original index 679954, selection on the full partial prefix of depth 13 and code 364686 returns the complete row with depth 13, base-four code 364686, original node 679954, kind 2, reserved field 0, 1349 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26929", "selected_cut_26929", "Selected cut at depth 13, code 364735, node 680874",
                "At remaining fuel 8 and original index 680874, selection on the full partial prefix of depth 13 and code 364735 returns the complete row with depth 13, base-four code 364735, original node 680874, kind 2, reserved field 0, 701 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91171-679963", "unmarked_context_12_91171_679963", "Unmarked parent at depth 12, code 91171",
                "The frontier Boolean is false at remaining fuel 9, original node 679963, the whole prefixCache at depth 12 and code 91171, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-5698-680877", "unmarked_context_10_5698_680877", "Unmarked parent at depth 10, code 5698",
                "The frontier Boolean is false at remaining fuel 11, original node 680877, the whole prefixCache at depth 10 and code 5698, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91171-679963", "node_context_12_91171_679963", "Original split at fuel 9 and node 679963",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 679905, 679937, 679954, 679962. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-5698-680877", "node_context_10_5698_680877", "Original split at fuel 11 and node 680877",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 679964, 680233, 680570, 680876. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-364686-679954", "context_13_364686_679954", "Context at depth 13, code 364686, node 679954",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 364686 and original node 679954, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-5698-680877", "context_10_5698_680877", "Context at depth 10, code 5698, node 680877",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 5698 and original node 680877, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_22792_679964, context_11_22793_680233, context_11_22794_680570, context_11_22795_680876.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
