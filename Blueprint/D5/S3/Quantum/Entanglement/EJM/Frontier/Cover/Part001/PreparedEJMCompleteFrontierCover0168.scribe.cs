using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0168Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0168.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0168",
        H("Original frontier context coverage 0168"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08067", "selected_cut_08067", "Selected cut at depth 13, code 91296, node 229413",
                "At remaining fuel 8 and original index 229413, selection on the full partial prefix of depth 13 and code 91296 returns the complete row with depth 13, base-four code 91296, original node 229413, kind 2, reserved field 0, 1541 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08114", "selected_cut_08114", "Selected cut at depth 13, code 91343, node 230354",
                "At remaining fuel 8 and original index 230354, selection on the full partial prefix of depth 13 and code 91343 returns the complete row with depth 13, base-four code 91343, original node 230354, kind 2, reserved field 0, 981 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5705-229385", "unmarked_context_11_5705_229385", "Unmarked parent at depth 11, code 5705",
                "The frontier Boolean is false at remaining fuel 10, original node 229385, the whole prefixCache at depth 11 and code 5705, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22835-230355", "unmarked_context_12_22835_230355", "Unmarked parent at depth 12, code 22835",
                "The frontier Boolean is false at remaining fuel 9, original node 230355, the whole prefixCache at depth 12 and code 22835, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5705-229385", "node_context_11_5705_229385", "Original split at fuel 10 and node 229385",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 229167, 229236, 229305, 229384. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22835-230355", "node_context_12_22835_230355", "Original split at fuel 9 and node 230355",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 230286, 230324, 230347, 230354. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5705-229385", "context_11_5705_229385", "Context at depth 11, code 5705, node 229385",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5705 and original node 229385, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_22820_229167, context_12_22821_229236, context_12_22822_229305, context_12_22823_229384.", DescribeRole.Theorem),
            Node("context-12-22835-230355", "context_12_22835_230355", "Context at depth 12, code 22835, node 230355",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22835 and original node 230355, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_91340_230286, context_13_91341_230324, context_13_91342_230347, context_13_91343_230354.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
