using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0762Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0762.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0762",
        H("Original frontier context coverage 0762"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36579", "selected_cut_36579", "Selected cut at depth 12, code 289554, node 970550",
                "At remaining fuel 9 and original index 970550, selection on the full partial prefix of depth 12 and code 289554 returns the complete row with depth 12, base-four code 289554, original node 970550, kind 2, reserved field 0, 3893 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36626", "selected_cut_36626", "Selected cut at depth 12, code 289604, node 972624",
                "At remaining fuel 9 and original index 972624, selection on the full partial prefix of depth 12 and code 289604 returns the complete row with depth 12, base-four code 289604, original node 972624, kind 2, reserved field 0, 2601 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-72388-970609", "unmarked_context_11_72388_970609", "Unmarked parent at depth 11, code 72388",
                "The frontier Boolean is false at remaining fuel 10, original node 970609, the whole prefixCache at depth 11 and code 72388, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-72400-972581", "unmarked_context_11_72400_972581", "Unmarked parent at depth 11, code 72400",
                "The frontier Boolean is false at remaining fuel 10, original node 972581, the whole prefixCache at depth 11 and code 72400, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-72388-970609", "node_context_11_72388_970609", "Original split at fuel 10 and node 970609",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 970432, 970492, 970550, 970608. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-72400-972581", "node_context_11_72400_972581", "Original split at fuel 10 and node 972581",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 972487, 896706, 972537, 972580. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-289554-970550", "context_12_289554_970550", "Context at depth 12, code 289554, node 970550",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 289554 and original node 970550, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-289604-972624", "context_12_289604_972624", "Context at depth 12, code 289604, node 972624",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 289604 and original node 972624, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
