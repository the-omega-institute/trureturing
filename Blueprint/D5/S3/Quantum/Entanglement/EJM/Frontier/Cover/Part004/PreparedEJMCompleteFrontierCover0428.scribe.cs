using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0428Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0428.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0428",
        H("Original frontier context coverage 0428"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20547", "selected_cut_20547", "Selected cut at depth 13, code 296151, node 527015",
                "At remaining fuel 8 and original index 527015, selection on the full partial prefix of depth 13 and code 296151 returns the complete row with depth 13, base-four code 296151, original node 527015, kind 2, reserved field 0, 1341 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20594", "selected_cut_20594", "Selected cut at depth 13, code 296207, node 527698",
                "At remaining fuel 8 and original index 527698, selection on the full partial prefix of depth 13 and code 296207 returns the complete row with depth 13, base-four code 296207, original node 527698, kind 2, reserved field 0, 1113 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-74037-527016", "unmarked_context_12_74037_527016", "Unmarked parent at depth 12, code 74037",
                "The frontier Boolean is false at remaining fuel 9, original node 527016, the whole prefixCache at depth 12 and code 74037, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-74050-527642", "unmarked_context_12_74050_527642", "Unmarked parent at depth 12, code 74050",
                "The frontier Boolean is false at remaining fuel 9, original node 527642, the whole prefixCache at depth 12 and code 74050, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-74037-527016", "node_context_12_74037_527016", "Original split at fuel 9 and node 527016",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 526932, 526964, 527002, 527015. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-74050-527642", "node_context_12_74050_527642", "Original split at fuel 9 and node 527642",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 527608, 527629, 527641. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-296151-527015", "context_13_296151_527015", "Context at depth 13, code 296151, node 527015",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 296151 and original node 527015, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-296207-527698", "context_13_296207_527698", "Context at depth 13, code 296207, node 527698",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 296207 and original node 527698, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
