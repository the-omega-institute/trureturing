using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0918Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0918.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0918",
        H("Original frontier context coverage 0918"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44068", "selected_cut_44068", "Selected cut at depth 11, code 88288, node 907917",
                "At remaining fuel 10 and original index 907917, selection on the full partial prefix of depth 11 and code 88288 returns the complete row with depth 11, base-four code 88288, original node 907917, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44114", "selected_cut_44114", "Selected cut at depth 12, code 353309, node 1211258",
                "At remaining fuel 9 and original index 1211258, selection on the full partial prefix of depth 12 and code 353309 returns the complete row with depth 12, base-four code 353309, original node 1211258, kind 2, reserved field 0, 2081 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22071-1209511", "unmarked_context_10_22071_1209511", "Unmarked parent at depth 10, code 22071",
                "The frontier Boolean is false at remaining fuel 11, original node 1209511, the whole prefixCache at depth 10 and code 22071, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88326-1211223", "unmarked_context_11_88326_1211223", "Unmarked parent at depth 11, code 88326",
                "The frontier Boolean is false at remaining fuel 10, original node 1211223, the whole prefixCache at depth 11 and code 88326, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22071-1209511", "node_context_10_22071_1209511", "Original split at fuel 11 and node 1209511",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1209341, 1209408, 1209483, 1209510. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88326-1211223", "node_context_11_88326_1211223", "Original split at fuel 10 and node 1211223",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 449505, 1211109, 1211156, 1211222. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-22071-1209511", "context_10_22071_1209511", "Context at depth 10, code 22071, node 1209511",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22071 and original node 1209511, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_88284_1209341, context_11_88285_1209408, context_11_88286_1209483, context_11_88287_1209510.", DescribeRole.Theorem),
            Node("context-12-353309-1211258", "context_12_353309_1211258", "Context at depth 12, code 353309, node 1211258",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 353309 and original node 1211258, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
