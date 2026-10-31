using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1075Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1075.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1075",
        H("Original frontier context coverage 1075"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51603", "selected_cut_51603", "Selected cut at depth 9, code 17691, node 1490302",
                "At remaining fuel 12 and original index 1490302, selection on the full partial prefix of depth 9 and code 17691 returns the complete row with depth 9, base-four code 17691, original node 1490302, kind 2, reserved field 0, 2933 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51650", "selected_cut_51650", "Selected cut at depth 12, code 1133345, node 1491855",
                "At remaining fuel 9 and original index 1491855, selection on the full partial prefix of depth 12 and code 1133345 returns the complete row with depth 12, base-four code 1133345, original node 1491855, kind 2, reserved field 0, 1725 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-17690-1490258", "unmarked_context_9_17690_1490258", "Unmarked parent at depth 9, code 17690",
                "The frontier Boolean is false at remaining fuel 12, original node 1490258, the whole prefixCache at depth 9 and code 17690, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-70833-1491818", "unmarked_context_10_70833_1491818", "Unmarked parent at depth 10, code 70833",
                "The frontier Boolean is false at remaining fuel 11, original node 1491818, the whole prefixCache at depth 10 and code 70833, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-17690-1490258", "node_context_9_17690_1490258", "Original split at fuel 12 and node 1490258",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1490156, 1490224, 1469103, 1490257. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-70833-1491818", "node_context_10_70833_1491818", "Original split at fuel 11 and node 1491818",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1491671, 1468419, 1491741, 1491817. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-17690-1490258", "context_9_17690_1490258", "Context at depth 9, code 17690, node 1490258",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 17690 and original node 1490258, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_70760_1490156, context_10_70761_1490224, context_10_70762_1469103, context_10_70763_1490257.", DescribeRole.Theorem),
            Node("context-12-1133345-1491855", "context_12_1133345_1491855", "Context at depth 12, code 1133345, node 1491855",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 1133345 and original node 1491855, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
