using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0161Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0161.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0161",
        H("Original frontier context coverage 0161"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07731", "selected_cut_07731", "Selected cut at depth 12, code 22626, node 221704",
                "At remaining fuel 9 and original index 221704, selection on the full partial prefix of depth 12 and code 22626 returns the complete row with depth 12, base-four code 22626, original node 221704, kind 2, reserved field 0, 4033 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07778", "selected_cut_07778", "Selected cut at depth 13, code 90566, node 222670",
                "At remaining fuel 8 and original index 222670, selection on the full partial prefix of depth 13 and code 90566 returns the complete row with depth 13, base-four code 90566, original node 222670, kind 2, reserved field 0, 2337 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22625-221657", "unmarked_context_12_22625_221657", "Unmarked parent at depth 12, code 22625",
                "The frontier Boolean is false at remaining fuel 9, original node 221657, the whole prefixCache at depth 12 and code 22625, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22640-222630", "unmarked_context_12_22640_222630", "Unmarked parent at depth 12, code 22640",
                "The frontier Boolean is false at remaining fuel 9, original node 222630, the whole prefixCache at depth 12 and code 22640, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22625-221657", "node_context_12_22625_221657", "Original split at fuel 9 and node 221657",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 221623, 221644, 221656. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22640-222630", "node_context_12_22640_222630", "Original split at fuel 9 and node 222630",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 222566, 222609, 222629. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-22625-221657", "context_12_22625_221657", "Context at depth 12, code 22625, node 221657",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22625 and original node 221657, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_90500_3444, context_13_90501_221623, context_13_90502_221644, context_13_90503_221656.", DescribeRole.Theorem),
            Node("context-13-90566-222670", "context_13_90566_222670", "Context at depth 13, code 90566, node 222670",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90566 and original node 222670, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
