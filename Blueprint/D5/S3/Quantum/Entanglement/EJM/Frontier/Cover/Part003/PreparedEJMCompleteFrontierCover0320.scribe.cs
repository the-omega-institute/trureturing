using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0320Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0320.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0320",
        H("Original frontier context coverage 0320"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15362", "selected_cut_15362", "Selected cut at depth 13, code 110852, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 110852 returns the complete row with depth 13, base-four code 110852, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15410", "selected_cut_15410", "Selected cut at depth 13, code 110903, node 395113",
                "At remaining fuel 8 and original index 395113, selection on the full partial prefix of depth 13 and code 110903 returns the complete row with depth 13, base-four code 110903, original node 395113, kind 2, reserved field 0, 1025 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27713-394283", "unmarked_context_12_27713_394283", "Unmarked parent at depth 12, code 27713",
                "The frontier Boolean is false at remaining fuel 9, original node 394283, the whole prefixCache at depth 12 and code 27713, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27725-395114", "unmarked_context_12_27725_395114", "Unmarked parent at depth 12, code 27725",
                "The frontier Boolean is false at remaining fuel 9, original node 395114, the whole prefixCache at depth 12 and code 27725, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27713-394283", "node_context_12_27713_394283", "Original split at fuel 9 and node 394283",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 394239, 394268, 394282. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27725-395114", "node_context_12_27725_395114", "Original split at fuel 9 and node 395114",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 395086, 395108, 395113. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-110852-3444", "context_13_110852_3444", "Context at depth 13, code 110852, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 110852 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27725-395114", "context_12_27725_395114", "Context at depth 12, code 27725, node 395114",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27725 and original node 395114, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_110900_3444, context_13_110901_395086, context_13_110902_395108, context_13_110903_395113.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
