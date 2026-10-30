using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0888Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0888.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0888",
        H("Original frontier context coverage 0888"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42627", "selected_cut_42627", "Selected cut at depth 12, code 338445, node 1164607",
                "At remaining fuel 9 and original index 1164607, selection on the full partial prefix of depth 12 and code 338445 returns the complete row with depth 12, base-four code 338445, original node 1164607, kind 2, reserved field 0, 3065 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42674", "selected_cut_42674", "Selected cut at depth 12, code 338495, node 1120582",
                "At remaining fuel 9 and original index 1120582, selection on the full partial prefix of depth 12 and code 338495 returns the complete row with depth 12, base-four code 338495, original node 1120582, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84611-1164700", "unmarked_context_11_84611_1164700", "Unmarked parent at depth 11, code 84611",
                "The frontier Boolean is false at remaining fuel 10, original node 1164700, the whole prefixCache at depth 11 and code 84611, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21155-1166065", "unmarked_context_10_21155_1166065", "Unmarked parent at depth 10, code 21155",
                "The frontier Boolean is false at remaining fuel 11, original node 1166065, the whole prefixCache at depth 10 and code 21155, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84611-1164700", "node_context_11_84611_1164700", "Original split at fuel 10 and node 1164700",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1164607, 1164652, 1164699. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21155-1166065", "node_context_10_21155_1166065", "Original split at fuel 11 and node 1166065",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1165783, 1165929, 1166005, 1166064. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-338445-1164607", "context_12_338445_1164607", "Context at depth 12, code 338445, node 1164607",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 338445 and original node 1164607, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-21155-1166065", "context_10_21155_1166065", "Context at depth 10, code 21155, node 1166065",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21155 and original node 1166065, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_84620_1165783, context_11_84621_1165929, context_11_84622_1166005, context_11_84623_1166064.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
