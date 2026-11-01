using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0959Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0959.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0959",
        H("Original frontier context coverage 0959"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46035", "selected_cut_46035", "Selected cut at depth 12, code 369678, node 1281378",
                "At remaining fuel 9 and original index 1281378, selection on the full partial prefix of depth 12 and code 369678 returns the complete row with depth 12, base-four code 369678, original node 1281378, kind 2, reserved field 0, 3065 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46081", "selected_cut_46081", "Selected cut at depth 12, code 369727, node 1116246",
                "At remaining fuel 9 and original index 1116246, selection on the full partial prefix of depth 12 and code 369727 returns the complete row with depth 12, base-four code 369727, original node 1116246, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92419-1281379", "unmarked_context_11_92419_1281379", "Unmarked parent at depth 11, code 92419",
                "The frontier Boolean is false at remaining fuel 10, original node 1281379, the whole prefixCache at depth 11 and code 92419, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5776-1283167", "unmarked_context_9_5776_1283167", "Unmarked parent at depth 9, code 5776",
                "The frontier Boolean is false at remaining fuel 12, original node 1283167, the whole prefixCache at depth 9 and code 5776, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92419-1281379", "node_context_11_92419_1281379", "Original split at fuel 10 and node 1281379",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1281306, 1281378, 296530. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5776-1283167", "node_context_9_5776_1283167", "Original split at fuel 12 and node 1283167",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1281380, 1281918, 1282624, 1283166. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-369678-1281378", "context_12_369678_1281378", "Context at depth 12, code 369678, node 1281378",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 369678 and original node 1281378, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-5776-1283167", "context_9_5776_1283167", "Context at depth 9, code 5776, node 1283167",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 5776 and original node 1283167, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_23104_1281380, context_10_23105_1281918, context_10_23106_1282624, context_10_23107_1283166.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
