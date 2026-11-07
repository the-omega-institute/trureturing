using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0113Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0113.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0113",
        H("Original frontier context coverage 0113"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05426", "selected_cut_05426", "Selected cut at depth 12, code 20504, node 168592",
                "At remaining fuel 9 and original index 168592, selection on the full partial prefix of depth 12 and code 20504 returns the complete row with depth 12, base-four code 20504, original node 168592, kind 2, reserved field 0, 3833 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05472", "selected_cut_05472", "Selected cut at depth 12, code 20544, node 169790",
                "At remaining fuel 9 and original index 169790, selection on the full partial prefix of depth 12 and code 20544 returns the complete row with depth 12, base-four code 20544, original node 169790, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5125-168523", "unmarked_context_11_5125_168523", "Unmarked parent at depth 11, code 5125",
                "The frontier Boolean is false at remaining fuel 10, original node 168523, the whole prefixCache at depth 11 and code 5125, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-320-169789", "unmarked_context_9_320_169789", "Unmarked parent at depth 9, code 320",
                "The frontier Boolean is false at remaining fuel 12, original node 169789, the whole prefixCache at depth 9 and code 320, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5125-168523", "node_context_11_5125_168523", "Original split at fuel 10 and node 168523",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 168402, 168451, 168522, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-320-169789", "node_context_9_320_169789", "Original split at fuel 12 and node 169789",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 168194, 168835, 169788, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5125-168523", "context_11_5125_168523", "Context at depth 11, code 5125, node 168523",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5125 and original node 168523, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_20500_168402, context_12_20501_168451, context_12_20502_168522, context_12_20503_893.", DescribeRole.Theorem),
            Node("context-12-20544-169790", "context_12_20544_169790", "Context at depth 12, code 20544, node 169790",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 20544 and original node 169790, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
