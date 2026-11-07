using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0989Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0989.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0989",
        H("Original frontier context coverage 0989"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47476", "selected_cut_47476", "Selected cut at depth 10, code 23338, node 1328850",
                "At remaining fuel 11 and original index 1328850, selection on the full partial prefix of depth 10 and code 23338 returns the complete row with depth 10, base-four code 23338, original node 1328850, kind 2, reserved field 0, 1397 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47523", "selected_cut_47523", "Selected cut at depth 12, code 373551, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 373551 returns the complete row with depth 12, base-four code 373551, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23337-1328820", "unmarked_context_10_23337_1328820", "Unmarked parent at depth 10, code 23337",
                "The frontier Boolean is false at remaining fuel 11, original node 1328820, the whole prefixCache at depth 10 and code 23337, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93387-1330320", "unmarked_context_11_93387_1330320", "Unmarked parent at depth 11, code 93387",
                "The frontier Boolean is false at remaining fuel 10, original node 1330320, the whole prefixCache at depth 11 and code 93387, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23337-1328820", "node_context_10_23337_1328820", "Original split at fuel 11 and node 1328820",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1328705, 1328730, 1328777, 1328819. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93387-1330320", "node_context_11_93387_1330320", "Original split at fuel 10 and node 1330320",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1330209, 1330267, 1330319, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23337-1328820", "context_10_23337_1328820", "Context at depth 10, code 23337, node 1328820",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23337 and original node 1328820, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_93348_1328705, context_11_93349_1328730, context_11_93350_1328777, context_11_93351_1328819.", DescribeRole.Theorem),
            Node("context-11-93387-1330320", "context_11_93387_1330320", "Context at depth 11, code 93387, node 1330320",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93387 and original node 1330320, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_373548_1330209, context_12_373549_1330267, context_12_373550_1330319, context_12_373551_903806.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
