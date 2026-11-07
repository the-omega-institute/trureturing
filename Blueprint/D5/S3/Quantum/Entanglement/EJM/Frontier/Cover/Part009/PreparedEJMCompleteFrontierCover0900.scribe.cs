using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0900Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0900.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0900",
        H("Original frontier context coverage 0900"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43204", "selected_cut_43204", "Selected cut at depth 12, code 339556, node 1181305",
                "At remaining fuel 9 and original index 1181305, selection on the full partial prefix of depth 12 and code 339556 returns the complete row with depth 12, base-four code 339556, original node 1181305, kind 2, reserved field 0, 1897 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43251", "selected_cut_43251", "Selected cut at depth 10, code 21231, node 1182811",
                "At remaining fuel 11 and original index 1182811, selection on the full partial prefix of depth 10 and code 21231 returns the complete row with depth 10, base-four code 21231, original node 1182811, kind 2, reserved field 0, 253 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84888-1181274", "unmarked_context_11_84888_1181274", "Unmarked parent at depth 11, code 84888",
                "The frontier Boolean is false at remaining fuel 10, original node 1181274, the whole prefixCache at depth 11 and code 84888, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21228-1182704", "unmarked_context_10_21228_1182704", "Unmarked parent at depth 10, code 21228",
                "The frontier Boolean is false at remaining fuel 11, original node 1182704, the whole prefixCache at depth 10 and code 21228, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84888-1181274", "node_context_11_84888_1181274", "Original split at fuel 10 and node 1181274",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1181170, 1181198, 1181233, 1181273. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21228-1182704", "node_context_10_21228_1182704", "Original split at fuel 11 and node 1182704",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1182621, 1182661, 1182685, 1182703. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84888-1181274", "context_11_84888_1181274", "Context at depth 11, code 84888, node 1181274",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84888 and original node 1181274, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_339552_1181170, context_12_339553_1181198, context_12_339554_1181233, context_12_339555_1181273.", DescribeRole.Theorem),
            Node("context-10-21231-1182811", "context_10_21231_1182811", "Context at depth 10, code 21231, node 1182811",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21231 and original node 1182811, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
