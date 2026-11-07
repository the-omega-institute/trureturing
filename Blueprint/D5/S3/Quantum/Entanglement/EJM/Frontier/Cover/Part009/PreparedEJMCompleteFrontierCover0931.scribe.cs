using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0931Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0931.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0931",
        H("Original frontier context coverage 0931"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44692", "selected_cut_44692", "Selected cut at depth 12, code 354844, node 1231033",
                "At remaining fuel 9 and original index 1231033, selection on the full partial prefix of depth 12 and code 354844 returns the complete row with depth 12, base-four code 354844, original node 1231033, kind 2, reserved field 0, 2913 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44739", "selected_cut_44739", "Selected cut at depth 11, code 88731, node 1232788",
                "At remaining fuel 10 and original index 1232788, selection on the full partial prefix of depth 11 and code 88731 returns the complete row with depth 11, base-four code 88731, original node 1232788, kind 2, reserved field 0, 2709 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88710-1230982", "unmarked_context_11_88710_1230982", "Unmarked parent at depth 11, code 88710",
                "The frontier Boolean is false at remaining fuel 10, original node 1230982, the whole prefixCache at depth 11 and code 88710, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-22180-1232565", "unmarked_context_10_22180_1232565", "Unmarked parent at depth 10, code 22180",
                "The frontier Boolean is false at remaining fuel 11, original node 1232565, the whole prefixCache at depth 10 and code 22180, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88710-1230982", "node_context_11_88710_1230982", "Original split at fuel 10 and node 1230982",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1230872, 1230921, 893903, 1230981. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-22180-1232565", "node_context_10_22180_1232565", "Original split at fuel 11 and node 1232565",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1232311, 1232411, 1232479, 1232564. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-88710-1230982", "context_11_88710_1230982", "Context at depth 11, code 88710, node 1230982",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88710 and original node 1230982, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_354840_1230872, context_12_354841_1230921, context_12_354842_893903, context_12_354843_1230981.", DescribeRole.Theorem),
            Node("context-11-88731-1232788", "context_11_88731_1232788", "Context at depth 11, code 88731, node 1232788",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88731 and original node 1232788, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
