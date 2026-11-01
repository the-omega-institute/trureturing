using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0247Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0247.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0247",
        H("Original frontier context coverage 0247"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11859", "selected_cut_11859", "Selected cut at depth 13, code 103548, node 317100",
                "At remaining fuel 8 and original index 317100, selection on the full partial prefix of depth 13 and code 103548 returns the complete row with depth 13, base-four code 103548, original node 317100, kind 2, reserved field 0, 1653 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11906", "selected_cut_11906", "Selected cut at depth 13, code 103595, node 318027",
                "At remaining fuel 8 and original index 318027, selection on the full partial prefix of depth 13 and code 103595 returns the complete row with depth 13, base-four code 103595, original node 318027, kind 2, reserved field 0, 1021 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25887-317154", "unmarked_context_12_25887_317154", "Unmarked parent at depth 12, code 25887",
                "The frontier Boolean is false at remaining fuel 9, original node 317154, the whole prefixCache at depth 12 and code 25887, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25898-318028", "unmarked_context_12_25898_318028", "Unmarked parent at depth 12, code 25898",
                "The frontier Boolean is false at remaining fuel 9, original node 318028, the whole prefixCache at depth 12 and code 25898, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25887-317154", "node_context_12_25887_317154", "Original split at fuel 9 and node 317154",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 317100, 317124, 317146, 317153. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25898-318028", "node_context_12_25898_318028", "Original split at fuel 9 and node 318028",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 317969, 317997, 318016, 318027. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-103548-317100", "context_13_103548_317100", "Context at depth 13, code 103548, node 317100",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 103548 and original node 317100, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25898-318028", "context_12_25898_318028", "Context at depth 12, code 25898, node 318028",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25898 and original node 318028, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_103592_317969, context_13_103593_317997, context_13_103594_318016, context_13_103595_318027.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
