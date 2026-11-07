using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0493Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0493.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0493",
        H("Original frontier context coverage 0493"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23668", "selected_cut_23668", "Selected cut at depth 13, code 306376, node 598544",
                "At remaining fuel 8 and original index 598544, selection on the full partial prefix of depth 13 and code 306376 returns the complete row with depth 13, base-four code 306376, original node 598544, kind 2, reserved field 0, 493 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23714", "selected_cut_23714", "Selected cut at depth 13, code 306440, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 306440 returns the complete row with depth 13, base-four code 306440, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76593-598536", "unmarked_context_12_76593_598536", "Unmarked parent at depth 12, code 76593",
                "The frontier Boolean is false at remaining fuel 9, original node 598536, the whole prefixCache at depth 12 and code 76593, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1196-599138", "unmarked_context_9_1196_599138", "Unmarked parent at depth 9, code 1196",
                "The frontier Boolean is false at remaining fuel 12, original node 599138, the whole prefixCache at depth 9 and code 1196, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76593-598536", "node_context_12_76593_598536", "Original split at fuel 9 and node 598536",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 598469, 598508, 598528, 598535. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1196-599138", "node_context_9_1196_599138", "Original split at fuel 12 and node 599138",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 596221, 597630, 598461, 599137. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76593-598536", "context_12_76593_598536", "Context at depth 12, code 76593, node 598536",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76593 and original node 598536, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_306372_598469, context_13_306373_598508, context_13_306374_598528, context_13_306375_598535.", DescribeRole.Theorem),
            Node("context-13-306440-3444", "context_13_306440_3444", "Context at depth 13, code 306440, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 306440 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
