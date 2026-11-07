using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0452Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0452.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0452",
        H("Original frontier context coverage 0452"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21700", "selected_cut_21700", "Selected cut at depth 12, code 75199, node 555073",
                "At remaining fuel 9 and original index 555073, selection on the full partial prefix of depth 12 and code 75199 returns the complete row with depth 12, base-four code 75199, original node 555073, kind 2, reserved field 0, 957 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21745", "selected_cut_21745", "Selected cut at depth 12, code 75280, node 435160",
                "At remaining fuel 9 and original index 435160, selection on the full partial prefix of depth 12 and code 75280 returns the complete row with depth 12, base-four code 75280, original node 435160, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18799-555074", "unmarked_context_11_18799_555074", "Unmarked parent at depth 11, code 18799",
                "The frontier Boolean is false at remaining fuel 10, original node 555074, the whole prefixCache at depth 11 and code 18799, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4704-556296", "unmarked_context_10_4704_556296", "Unmarked parent at depth 10, code 4704",
                "The frontier Boolean is false at remaining fuel 11, original node 556296, the whole prefixCache at depth 10 and code 4704, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18799-555074", "node_context_11_18799_555074", "Original split at fuel 10 and node 555074",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 555038, 555047, 555062, 555073. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4704-556296", "node_context_10_4704_556296", "Original split at fuel 11 and node 556296",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 555681, 556025, 556295. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75199-555073", "context_12_75199_555073", "Context at depth 12, code 75199, node 555073",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75199 and original node 555073, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-75280-435160", "context_12_75280_435160", "Context at depth 12, code 75280, node 435160",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75280 and original node 435160, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
