using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0068Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0068.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0068",
        H("Original frontier context coverage 0068"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03266", "selected_cut_03266", "Selected cut at depth 13, code 27653, node 103081",
                "At remaining fuel 8 and original index 103081, selection on the full partial prefix of depth 13 and code 27653 returns the complete row with depth 13, base-four code 27653, original node 103081, kind 2, reserved field 0, 3973 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03314", "selected_cut_03314", "Selected cut at depth 14, code 110693, node 104585",
                "At remaining fuel 7 and original index 104585, selection on the full partial prefix of depth 14 and code 110693 returns the complete row with depth 14, base-four code 110693, original node 104585, kind 2, reserved field 0, 1261 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-6913-103161", "unmarked_context_12_6913_103161", "Unmarked parent at depth 12, code 6913",
                "The frontier Boolean is false at remaining fuel 9, original node 103161, the whole prefixCache at depth 12 and code 6913, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-27672-104541", "unmarked_context_13_27672_104541", "Unmarked parent at depth 13, code 27672",
                "The frontier Boolean is false at remaining fuel 8, original node 104541, the whole prefixCache at depth 13 and code 27672, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-6913-103161", "node_context_12_6913_103161", "Original split at fuel 9 and node 103161",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 102990, 103081, 103143, 103160. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-27672-104541", "node_context_13_27672_104541", "Original split at fuel 8 and node 104541",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 104459, 104485, 104521, 104540. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-27653-103081", "context_13_27653_103081", "Context at depth 13, code 27653, node 103081",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 27653 and original node 103081, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-110693-104585", "context_14_110693_104585", "Context at depth 14, code 110693, node 104585",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 110693 and original node 104585, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
