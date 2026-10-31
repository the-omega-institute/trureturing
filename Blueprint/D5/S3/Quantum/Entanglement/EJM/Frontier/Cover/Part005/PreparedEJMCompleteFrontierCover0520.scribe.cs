using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0520Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0520.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0520",
        H("Original frontier context coverage 0520"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24963", "selected_cut_24963", "Selected cut at depth 13, code 310308, node 630945",
                "At remaining fuel 8 and original index 630945, selection on the full partial prefix of depth 13 and code 310308 returns the complete row with depth 13, base-four code 310308, original node 630945, kind 2, reserved field 0, 3381 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25011", "selected_cut_25011", "Selected cut at depth 13, code 310383, node 632657",
                "At remaining fuel 8 and original index 632657, selection on the full partial prefix of depth 13 and code 310383 returns the complete row with depth 13, base-four code 310383, original node 632657, kind 2, reserved field 0, 801 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77577-631209", "unmarked_context_12_77577_631209", "Unmarked parent at depth 12, code 77577",
                "The frontier Boolean is false at remaining fuel 9, original node 631209, the whole prefixCache at depth 12 and code 77577, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77595-632658", "unmarked_context_12_77595_632658", "Unmarked parent at depth 12, code 77595",
                "The frontier Boolean is false at remaining fuel 9, original node 632658, the whole prefixCache at depth 12 and code 77595, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77577-631209", "node_context_12_77577_631209", "Original split at fuel 9 and node 631209",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 630945, 631049, 631176, 631208. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77595-632658", "node_context_12_77595_632658", "Original split at fuel 9 and node 632658",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 632577, 632617, 632643, 632657. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-310308-630945", "context_13_310308_630945", "Context at depth 13, code 310308, node 630945",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 310308 and original node 630945, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-77595-632658", "context_12_77595_632658", "Context at depth 12, code 77595, node 632658",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77595 and original node 632658, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_310380_632577, context_13_310381_632617, context_13_310382_632643, context_13_310383_632657.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
