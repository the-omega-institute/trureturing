using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0921Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0921.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0921",
        H("Original frontier context coverage 0921"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44211", "selected_cut_44211", "Selected cut at depth 12, code 353550, node 1214162",
                "At remaining fuel 9 and original index 1214162, selection on the full partial prefix of depth 12 and code 353550 returns the complete row with depth 12, base-four code 353550, original node 1214162, kind 2, reserved field 0, 2857 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44257", "selected_cut_44257", "Selected cut at depth 12, code 353599, node 1116246",
                "At remaining fuel 9 and original index 1116246, selection on the full partial prefix of depth 12 and code 353599 returns the complete row with depth 12, base-four code 353599, original node 1116246, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88387-1214221", "unmarked_context_11_88387_1214221", "Unmarked parent at depth 11, code 88387",
                "The frontier Boolean is false at remaining fuel 10, original node 1214221, the whole prefixCache at depth 11 and code 88387, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5524-1215920", "unmarked_context_9_5524_1215920", "Unmarked parent at depth 9, code 5524",
                "The frontier Boolean is false at remaining fuel 12, original node 1215920, the whole prefixCache at depth 9 and code 5524, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88387-1214221", "node_context_11_88387_1214221", "Original split at fuel 10 and node 1214221",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1214111, 1214162, 1214220. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5524-1215920", "node_context_9_5524_1215920", "Original split at fuel 12 and node 1215920",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1214222, 1214712, 1215336, 1215919. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-353550-1214162", "context_12_353550_1214162", "Context at depth 12, code 353550, node 1214162",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 353550 and original node 1214162, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-5524-1215920", "context_9_5524_1215920", "Context at depth 9, code 5524, node 1215920",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 5524 and original node 1215920, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_22096_1214222, context_10_22097_1214712, context_10_22098_1215336, context_10_22099_1215919.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
