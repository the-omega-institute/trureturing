using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0411Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0411.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0411",
        H("Original frontier context coverage 0411"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19732", "selected_cut_19732", "Selected cut at depth 13, code 289213, node 504342",
                "At remaining fuel 8 and original index 504342, selection on the full partial prefix of depth 13 and code 289213 returns the complete row with depth 13, base-four code 289213, original node 504342, kind 2, reserved field 0, 849 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19778", "selected_cut_19778", "Selected cut at depth 12, code 72344, node 505840",
                "At remaining fuel 9 and original index 505840, selection on the full partial prefix of depth 12 and code 72344 returns the complete row with depth 12, base-four code 72344, original node 505840, kind 2, reserved field 0, 1625 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72303-504378", "unmarked_context_12_72303_504378", "Unmarked parent at depth 12, code 72303",
                "The frontier Boolean is false at remaining fuel 9, original node 504378, the whole prefixCache at depth 12 and code 72303, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18085-505823", "unmarked_context_11_18085_505823", "Unmarked parent at depth 11, code 18085",
                "The frontier Boolean is false at remaining fuel 10, original node 505823, the whole prefixCache at depth 11 and code 18085, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72303-504378", "node_context_12_72303_504378", "Original split at fuel 9 and node 504378",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 504342, 504364, 504377. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18085-505823", "node_context_11_18085_505823", "Original split at fuel 10 and node 505823",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 505735, 505761, 505795, 505822. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-289213-504342", "context_13_289213_504342", "Context at depth 13, code 289213, node 504342",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 289213 and original node 504342, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-72344-505840", "context_12_72344_505840", "Context at depth 12, code 72344, node 505840",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72344 and original node 505840, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
