using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1064Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1064.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1064",
        H("Original frontier context coverage 1064"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 45 exact cut-selection equations, and 19 literal split equations paired with 19 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51077", "selected_cut_51077", "Selected cut at depth 11, code 114335, node 1464294",
                "At remaining fuel 10 and original index 1464294, selection on the full partial prefix of depth 11 and code 114335 returns the complete row with depth 11, base-four code 114335, original node 1464294, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51121", "selected_cut_51121", "Selected cut at depth 10, code 69655, node 3440",
                "At remaining fuel 11 and original index 3440, selection on the full partial prefix of depth 10 and code 69655 returns the complete row with depth 10, base-four code 69655, original node 3440, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-28583-1467735", "unmarked_context_10_28583_1467735", "Unmarked parent at depth 10, code 28583",
                "The frontier Boolean is false at remaining fuel 11, original node 1467735, the whole prefixCache at depth 10 and code 28583, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-69654-1469808", "unmarked_context_10_69654_1469808", "Unmarked parent at depth 10, code 69654",
                "The frontier Boolean is false at remaining fuel 11, original node 1469808, the whole prefixCache at depth 10 and code 69654, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-28583-1467735", "node_context_10_28583_1467735", "Original split at fuel 11 and node 1467735",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1467623, 1467688, 1467734, 1464294. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-69654-1469808", "node_context_10_69654_1469808", "Original split at fuel 11 and node 1469808",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1469702, 1469763, 1468743, 1469807. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-114335-1464294", "context_11_114335_1464294", "Context at depth 11, code 114335, node 1464294",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 114335 and original node 1464294, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-69655-3440", "context_10_69655_3440", "Context at depth 10, code 69655, node 3440",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 69655 and original node 3440, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
