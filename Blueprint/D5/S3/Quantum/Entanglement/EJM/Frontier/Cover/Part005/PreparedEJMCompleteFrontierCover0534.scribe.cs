using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0534Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0534.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0534",
        H("Original frontier context coverage 0534"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25635", "selected_cut_25635", "Selected cut at depth 13, code 352299, node 649481",
                "At remaining fuel 8 and original index 649481, selection on the full partial prefix of depth 13 and code 352299 returns the complete row with depth 13, base-four code 352299, original node 649481, kind 2, reserved field 0, 141 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25681", "selected_cut_25681", "Selected cut at depth 13, code 352351, node 650901",
                "At remaining fuel 8 and original index 650901, selection on the full partial prefix of depth 13 and code 352351 returns the complete row with depth 13, base-four code 352351, original node 650901, kind 2, reserved field 0, 853 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88074-649482", "unmarked_context_12_88074_649482", "Unmarked parent at depth 12, code 88074",
                "The frontier Boolean is false at remaining fuel 9, original node 649482, the whole prefixCache at depth 12 and code 88074, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22021-650903", "unmarked_context_11_22021_650903", "Unmarked parent at depth 11, code 22021",
                "The frontier Boolean is false at remaining fuel 10, original node 650903, the whole prefixCache at depth 11 and code 22021, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88074-649482", "node_context_12_88074_649482", "Original split at fuel 9 and node 649482",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 649408, 649458, 649478, 649481. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22021-650903", "node_context_11_22021_650903", "Original split at fuel 10 and node 650903",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 650600, 650685, 650784, 650902. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-352299-649481", "context_13_352299_649481", "Context at depth 13, code 352299, node 649481",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 352299 and original node 649481, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-22021-650903", "context_11_22021_650903", "Context at depth 11, code 22021, node 650903",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 22021 and original node 650903, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_88084_650600, context_12_88085_650685, context_12_88086_650784, context_12_88087_650902.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
