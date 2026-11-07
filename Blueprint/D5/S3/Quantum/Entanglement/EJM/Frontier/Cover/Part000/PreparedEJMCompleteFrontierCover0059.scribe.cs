using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0059Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0059.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0059",
        H("Original frontier context coverage 0059"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02835", "selected_cut_02835", "Selected cut at depth 14, code 106548, node 87262",
                "At remaining fuel 7 and original index 87262, selection on the full partial prefix of depth 14 and code 106548 returns the complete row with depth 14, base-four code 106548, original node 87262, kind 2, reserved field 0, 1137 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02881", "selected_cut_02881", "Selected cut at depth 12, code 6664, node 88909",
                "At remaining fuel 9 and original index 88909, selection on the full partial prefix of depth 12 and code 6664 returns the complete row with depth 12, base-four code 6664, original node 88909, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-26636-87246", "unmarked_context_13_26636_87246", "Unmarked parent at depth 13, code 26636",
                "The frontier Boolean is false at remaining fuel 8, original node 87246, the whole prefixCache at depth 13 and code 26636, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1665-88908", "unmarked_context_11_1665_88908", "Unmarked parent at depth 11, code 1665",
                "The frontier Boolean is false at remaining fuel 10, original node 88908, the whole prefixCache at depth 11 and code 1665, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-26636-87246", "node_context_13_26636_87246", "Original split at fuel 8 and node 87246",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 87166, 87195, 87221, 87245. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1665-88908", "node_context_11_1665_88908", "Original split at fuel 10 and node 88908",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 87913, 88248, 88560, 88907. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-26636-87246", "context_13_26636_87246", "Context at depth 13, code 26636, node 87246",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 26636 and original node 87246, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_106544_87166, context_14_106545_87195, context_14_106546_87221, context_14_106547_87245.", DescribeRole.Theorem),
            Node("context-12-6664-88909", "context_12_6664_88909", "Context at depth 12, code 6664, node 88909",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 6664 and original node 88909, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
