using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0097Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0097.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0097",
        H("Original frontier context coverage 0097"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04658", "selected_cut_04658", "Selected cut at depth 13, code 74849, node 150191",
                "At remaining fuel 8 and original index 150191, selection on the full partial prefix of depth 13 and code 74849 returns the complete row with depth 13, base-four code 74849, original node 150191, kind 2, reserved field 0, 2517 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04705", "selected_cut_04705", "Selected cut at depth 13, code 74896, node 151215",
                "At remaining fuel 8 and original index 151215, selection on the full partial prefix of depth 13 and code 74896 returns the complete row with depth 13, base-four code 74896, original node 151215, kind 2, reserved field 0, 1169 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18712-150222", "unmarked_context_12_18712_150222", "Unmarked parent at depth 12, code 18712",
                "The frontier Boolean is false at remaining fuel 9, original node 150222, the whole prefixCache at depth 12 and code 18712, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4680-151198", "unmarked_context_11_4680_151198", "Unmarked parent at depth 11, code 4680",
                "The frontier Boolean is false at remaining fuel 10, original node 151198, the whole prefixCache at depth 11 and code 4680, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18712-150222", "node_context_12_18712_150222", "Original split at fuel 9 and node 150222",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 150167, 150191, 150213, 150221. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4680-151198", "node_context_11_4680_151198", "Original split at fuel 10 and node 151198",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 150950, 151023, 151108, 151197. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-74849-150191", "context_13_74849_150191", "Context at depth 13, code 74849, node 150191",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 74849 and original node 150191, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-74896-151215", "context_13_74896_151215", "Context at depth 13, code 74896, node 151215",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 74896 and original node 151215, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
