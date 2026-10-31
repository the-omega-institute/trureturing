using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0492Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0492.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0492",
        H("Original frontier context coverage 0492"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23620", "selected_cut_23620", "Selected cut at depth 13, code 306316, node 597780",
                "At remaining fuel 8 and original index 597780, selection on the full partial prefix of depth 13 and code 306316 returns the complete row with depth 13, base-four code 306316, original node 597780, kind 2, reserved field 0, 837 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23667", "selected_cut_23667", "Selected cut at depth 13, code 306375, node 598535",
                "At remaining fuel 8 and original index 598535, selection on the full partial prefix of depth 13 and code 306375 returns the complete row with depth 13, base-four code 306375, original node 598535, kind 2, reserved field 0, 897 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76578-597763", "unmarked_context_12_76578_597763", "Unmarked parent at depth 12, code 76578",
                "The frontier Boolean is false at remaining fuel 9, original node 597763, the whole prefixCache at depth 12 and code 76578, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4786-598461", "unmarked_context_10_4786_598461", "Unmarked parent at depth 10, code 4786",
                "The frontier Boolean is false at remaining fuel 11, original node 598461, the whole prefixCache at depth 10 and code 4786, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76578-597763", "node_context_12_76578_597763", "Original split at fuel 9 and node 597763",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 597714, 597740, 597758, 597762. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4786-598461", "node_context_10_4786_598461", "Original split at fuel 11 and node 598461",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 597827, 598116, 598266, 598460. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76578-597763", "context_12_76578_597763", "Context at depth 12, code 76578, node 597763",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76578 and original node 597763, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_306312_597714, context_13_306313_597740, context_13_306314_597758, context_13_306315_597762.", DescribeRole.Theorem),
            Node("context-13-306375-598535", "context_13_306375_598535", "Context at depth 13, code 306375, node 598535",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 306375 and original node 598535, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
