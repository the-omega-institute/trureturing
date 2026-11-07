using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0216Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0216.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0216",
        H("Original frontier context coverage 0216"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10371", "selected_cut_10371", "Selected cut at depth 12, code 25008, node 282346",
                "At remaining fuel 9 and original index 282346, selection on the full partial prefix of depth 12 and code 25008 returns the complete row with depth 12, base-four code 25008, original node 282346, kind 2, reserved field 0, 1101 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10417", "selected_cut_10417", "Selected cut at depth 13, code 100387, node 283405",
                "At remaining fuel 8 and original index 283405, selection on the full partial prefix of depth 13 and code 100387 returns the complete row with depth 13, base-four code 100387, original node 283405, kind 2, reserved field 0, 953 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1562-282333", "unmarked_context_10_1562_282333", "Unmarked parent at depth 10, code 1562",
                "The frontier Boolean is false at remaining fuel 11, original node 282333, the whole prefixCache at depth 10 and code 1562, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25096-283406", "unmarked_context_12_25096_283406", "Unmarked parent at depth 12, code 25096",
                "The frontier Boolean is false at remaining fuel 9, original node 283406, the whole prefixCache at depth 12 and code 25096, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1562-282333", "node_context_10_1562_282333", "Original split at fuel 11 and node 282333",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 282116, 282191, 282260, 282332. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25096-283406", "node_context_12_25096_283406", "Original split at fuel 9 and node 283406",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 283343, 283374, 283395, 283405. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-1562-282333", "context_10_1562_282333", "Context at depth 10, code 1562, node 282333",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1562 and original node 282333, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6248_282116, context_11_6249_282191, context_11_6250_282260, context_11_6251_282332.", DescribeRole.Theorem),
            Node("context-12-25096-283406", "context_12_25096_283406", "Context at depth 12, code 25096, node 283406",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25096 and original node 283406, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_100384_283343, context_13_100385_283374, context_13_100386_283395, context_13_100387_283405.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
