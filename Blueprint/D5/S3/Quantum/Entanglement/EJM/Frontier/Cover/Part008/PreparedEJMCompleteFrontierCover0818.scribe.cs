using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0818Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0818.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0818",
        H("Original frontier context coverage 0818"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39268", "selected_cut_39268", "Selected cut at depth 11, code 75712, node 1064787",
                "At remaining fuel 10 and original index 1064787, selection on the full partial prefix of depth 11 and code 75712 returns the complete row with depth 11, base-four code 75712, original node 1064787, kind 2, reserved field 0, 3957 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39314", "selected_cut_39314", "Selected cut at depth 12, code 302867, node 1065988",
                "At remaining fuel 9 and original index 1065988, selection on the full partial prefix of depth 12 and code 302867 returns the complete row with depth 12, base-four code 302867, original node 1065988, kind 2, reserved field 0, 3517 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-4731-1064723", "unmarked_context_9_4731_1064723", "Unmarked parent at depth 9, code 4731",
                "The frontier Boolean is false at remaining fuel 12, original node 1064723, the whole prefixCache at depth 9 and code 4731, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75716-1065989", "unmarked_context_11_75716_1065989", "Unmarked parent at depth 11, code 75716",
                "The frontier Boolean is false at remaining fuel 10, original node 1065989, the whole prefixCache at depth 11 and code 75716, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-4731-1064723", "node_context_9_4731_1064723", "Original split at fuel 12 and node 1064723",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1064574, 1064640, 1064691, 1064722. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75716-1065989", "node_context_11_75716_1065989", "Original split at fuel 10 and node 1065989",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1065809, 1065880, 1065939, 1065988. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-4731-1064723", "context_9_4731_1064723", "Context at depth 9, code 4731, node 1064723",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 4731 and original node 1064723, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_18924_1064574, context_10_18925_1064640, context_10_18926_1064691, context_10_18927_1064722.", DescribeRole.Theorem),
            Node("context-11-75716-1065989", "context_11_75716_1065989", "Context at depth 11, code 75716, node 1065989",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75716 and original node 1065989, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_302864_1065809, context_12_302865_1065880, context_12_302866_1065939, context_12_302867_1065988.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
