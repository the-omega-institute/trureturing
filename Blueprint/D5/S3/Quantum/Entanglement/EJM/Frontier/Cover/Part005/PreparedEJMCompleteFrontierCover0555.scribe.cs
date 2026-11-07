using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0555Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0555.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0555",
        H("Original frontier context coverage 0555"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26644", "selected_cut_26644", "Selected cut at depth 12, code 88912, node 673425",
                "At remaining fuel 9 and original index 673425, selection on the full partial prefix of depth 12 and code 88912 returns the complete row with depth 12, base-four code 88912, original node 673425, kind 2, reserved field 0, 3409 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26692", "selected_cut_26692", "Selected cut at depth 13, code 355774, node 674785",
                "At remaining fuel 8 and original index 674785, selection on the full partial prefix of depth 13 and code 355774 returns the complete row with depth 13, base-four code 355774, original node 674785, kind 2, reserved field 0, 2305 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-22227-673380", "unmarked_context_11_22227_673380", "Unmarked parent at depth 11, code 22227",
                "The frontier Boolean is false at remaining fuel 10, original node 673380, the whole prefixCache at depth 11 and code 22227, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22234-674635", "unmarked_context_11_22234_674635", "Unmarked parent at depth 11, code 22234",
                "The frontier Boolean is false at remaining fuel 10, original node 674635, the whole prefixCache at depth 11 and code 22234, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-22227-673380", "node_context_11_22227_673380", "Original split at fuel 10 and node 673380",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 673157, 673233, 673287, 673379. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22234-674635", "node_context_11_22234_674635", "Original split at fuel 10 and node 674635",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 674439, 674583, 474208, 674634. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-22227-673380", "context_11_22227_673380", "Context at depth 11, code 22227, node 673380",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 22227 and original node 673380, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_88908_673157, context_12_88909_673233, context_12_88910_673287, context_12_88911_673379.", DescribeRole.Theorem),
            Node("context-13-355774-674785", "context_13_355774_674785", "Context at depth 13, code 355774, node 674785",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 355774 and original node 674785, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
