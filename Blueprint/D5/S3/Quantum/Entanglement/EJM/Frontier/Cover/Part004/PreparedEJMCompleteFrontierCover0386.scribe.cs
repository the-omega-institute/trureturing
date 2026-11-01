using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0386Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0386.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0386",
        H("Original frontier context coverage 0386"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18531", "selected_cut_18531", "Selected cut at depth 13, code 286908, node 474609",
                "At remaining fuel 8 and original index 474609, selection on the full partial prefix of depth 13 and code 286908 returns the complete row with depth 13, base-four code 286908, original node 474609, kind 2, reserved field 0, 629 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18579", "selected_cut_18579", "Selected cut at depth 13, code 286959, node 475530",
                "At remaining fuel 8 and original index 475530, selection on the full partial prefix of depth 13 and code 286959 returns the complete row with depth 13, base-four code 286959, original node 475530, kind 2, reserved field 0, 801 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71727-474677", "unmarked_context_12_71727_474677", "Unmarked parent at depth 12, code 71727",
                "The frontier Boolean is false at remaining fuel 9, original node 474677, the whole prefixCache at depth 12 and code 71727, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71738-475455", "unmarked_context_12_71738_475455", "Unmarked parent at depth 12, code 71738",
                "The frontier Boolean is false at remaining fuel 9, original node 475455, the whole prefixCache at depth 12 and code 71738, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71727-474677", "node_context_12_71727_474677", "Original split at fuel 9 and node 474677",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 474609, 474649, 474670, 474676. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71738-475455", "node_context_12_71738_475455", "Original split at fuel 9 and node 475455",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 475395, 475430, 475448, 475454. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-286908-474609", "context_13_286908_474609", "Context at depth 13, code 286908, node 474609",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 286908 and original node 474609, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-286959-475530", "context_13_286959_475530", "Context at depth 13, code 286959, node 475530",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 286959 and original node 475530, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
