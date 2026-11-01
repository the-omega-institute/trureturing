using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0515Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0515.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0515",
        H("Original frontier context coverage 0515"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24723", "selected_cut_24723", "Selected cut at depth 12, code 77364, node 567386",
                "At remaining fuel 9 and original index 567386, selection on the full partial prefix of depth 12 and code 77364 returns the complete row with depth 12, base-four code 77364, original node 567386, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24771", "selected_cut_24771", "Selected cut at depth 13, code 309519, node 625528",
                "At remaining fuel 8 and original index 625528, selection on the full partial prefix of depth 13 and code 309519 returns the complete row with depth 13, base-four code 309519, original node 625528, kind 2, reserved field 0, 913 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77365-624670", "unmarked_context_12_77365_624670", "Unmarked parent at depth 12, code 77365",
                "The frontier Boolean is false at remaining fuel 9, original node 624670, the whole prefixCache at depth 12 and code 77365, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77378-625455", "unmarked_context_12_77378_625455", "Unmarked parent at depth 12, code 77378",
                "The frontier Boolean is false at remaining fuel 9, original node 625455, the whole prefixCache at depth 12 and code 77378, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77365-624670", "node_context_12_77365_624670", "Original split at fuel 9 and node 624670",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 624614, 624638, 624659, 624669. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77378-625455", "node_context_12_77378_625455", "Original split at fuel 9 and node 625455",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 625418, 625440, 625454. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-77364-567386", "context_12_77364_567386", "Context at depth 12, code 77364, node 567386",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77364 and original node 567386, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-309519-625528", "context_13_309519_625528", "Context at depth 13, code 309519, node 625528",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 309519 and original node 625528, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
