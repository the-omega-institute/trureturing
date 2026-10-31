using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0674Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0674.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0674",
        H("Original frontier context coverage 0674"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32355", "selected_cut_32355", "Selected cut at depth 13, code 433281, node 831696",
                "At remaining fuel 8 and original index 831696, selection on the full partial prefix of depth 13 and code 433281 returns the complete row with depth 13, base-four code 433281, original node 831696, kind 2, reserved field 0, 2761 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32403", "selected_cut_32403", "Selected cut at depth 13, code 433329, node 832815",
                "At remaining fuel 8 and original index 832815, selection on the full partial prefix of depth 13 and code 433329 returns the complete row with depth 13, base-four code 433329, original node 832815, kind 2, reserved field 0, 2117 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-108320-831723", "unmarked_context_12_108320_831723", "Unmarked parent at depth 12, code 108320",
                "The frontier Boolean is false at remaining fuel 9, original node 831723, the whole prefixCache at depth 12 and code 108320, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27082-832763", "unmarked_context_11_27082_832763", "Unmarked parent at depth 11, code 27082",
                "The frontier Boolean is false at remaining fuel 10, original node 832763, the whole prefixCache at depth 11 and code 27082, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-108320-831723", "node_context_12_108320_831723", "Original split at fuel 9 and node 831723",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 831640, 831696, 831712, 831722. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27082-832763", "node_context_11_27082_832763", "Original split at fuel 10 and node 832763",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 832559, 832630, 832699, 832762. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-433281-831696", "context_13_433281_831696", "Context at depth 13, code 433281, node 831696",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 433281 and original node 831696, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-433329-832815", "context_13_433329_832815", "Context at depth 13, code 433329, node 832815",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 433329 and original node 832815, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
