using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0648Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0648.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0648",
        H("Original frontier context coverage 0648"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31108", "selected_cut_31108", "Selected cut at depth 13, code 422071, node 792112",
                "At remaining fuel 8 and original index 792112, selection on the full partial prefix of depth 13 and code 422071 returns the complete row with depth 13, base-four code 422071, original node 792112, kind 2, reserved field 0, 689 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31154", "selected_cut_31154", "Selected cut at depth 13, code 422273, node 794131",
                "At remaining fuel 8 and original index 794131, selection on the full partial prefix of depth 13 and code 422273 returns the complete row with depth 13, base-four code 422273, original node 794131, kind 2, reserved field 0, 2065 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-105517-792113", "unmarked_context_12_105517_792113", "Unmarked parent at depth 12, code 105517",
                "The frontier Boolean is false at remaining fuel 9, original node 792113, the whole prefixCache at depth 12 and code 105517, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6597-794065", "unmarked_context_10_6597_794065", "Unmarked parent at depth 10, code 6597",
                "The frontier Boolean is false at remaining fuel 11, original node 794065, the whole prefixCache at depth 10 and code 6597, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-105517-792113", "node_context_12_105517_792113", "Original split at fuel 9 and node 792113",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 792049, 792085, 792106, 792112. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6597-794065", "node_context_10_6597_794065", "Original split at fuel 11 and node 794065",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 793699, 793907, 794023, 794064. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-422071-792112", "context_13_422071_792112", "Context at depth 13, code 422071, node 792112",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 422071 and original node 792112, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-422273-794131", "context_13_422273_794131", "Context at depth 13, code 422273, node 794131",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 422273 and original node 794131, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
