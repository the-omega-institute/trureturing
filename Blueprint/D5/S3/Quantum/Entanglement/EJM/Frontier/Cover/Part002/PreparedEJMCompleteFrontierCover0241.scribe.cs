using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0241Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0241.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0241",
        H("Original frontier context coverage 0241"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11571", "selected_cut_11571", "Selected cut at depth 13, code 102762, node 309188",
                "At remaining fuel 8 and original index 309188, selection on the full partial prefix of depth 13 and code 102762 returns the complete row with depth 13, base-four code 102762, original node 309188, kind 2, reserved field 0, 1729 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11617", "selected_cut_11617", "Selected cut at depth 12, code 25711, node 310375",
                "At remaining fuel 9 and original index 310375, selection on the full partial prefix of depth 12 and code 25711 returns the complete row with depth 12, base-four code 25711, original node 310375, kind 2, reserved field 0, 3513 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25690-309199", "unmarked_context_12_25690_309199", "Unmarked parent at depth 12, code 25690",
                "The frontier Boolean is false at remaining fuel 9, original node 309199, the whole prefixCache at depth 12 and code 25690, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1606-310377", "unmarked_context_10_1606_310377", "Unmarked parent at depth 10, code 1606",
                "The frontier Boolean is false at remaining fuel 11, original node 310377, the whole prefixCache at depth 10 and code 1606, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25690-309199", "node_context_12_25690_309199", "Original split at fuel 9 and node 309199",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 309164, 309188, 309198. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1606-310377", "node_context_10_1606_310377", "Original split at fuel 11 and node 310377",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 309782, 309919, 310151, 310376. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-102762-309188", "context_13_102762_309188", "Context at depth 13, code 102762, node 309188",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 102762 and original node 309188, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-1606-310377", "context_10_1606_310377", "Context at depth 10, code 1606, node 310377",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1606 and original node 310377, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6424_309782, context_11_6425_309919, context_11_6426_310151, context_11_6427_310376.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
