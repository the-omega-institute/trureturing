using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0096Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0096.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0096",
        H("Original frontier context coverage 0096"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04610", "selected_cut_04610", "Selected cut at depth 13, code 74801, node 148953",
                "At remaining fuel 8 and original index 148953, selection on the full partial prefix of depth 13 and code 74801 returns the complete row with depth 13, base-four code 74801, original node 148953, kind 2, reserved field 0, 3945 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04657", "selected_cut_04657", "Selected cut at depth 13, code 74848, node 150167",
                "At remaining fuel 8 and original index 150167, selection on the full partial prefix of depth 13 and code 74848 returns the complete row with depth 13, base-four code 74848, original node 150167, kind 2, reserved field 0, 1497 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18700-148990", "unmarked_context_12_18700_148990", "Unmarked parent at depth 12, code 18700",
                "The frontier Boolean is false at remaining fuel 9, original node 148990, the whole prefixCache at depth 12 and code 18700, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4677-150150", "unmarked_context_11_4677_150150", "Unmarked parent at depth 11, code 4677",
                "The frontier Boolean is false at remaining fuel 10, original node 150150, the whole prefixCache at depth 11 and code 4677, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18700-148990", "node_context_12_18700_148990", "Original split at fuel 9 and node 148990",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 148899, 148953, 148974, 148989. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4677-150150", "node_context_11_4677_150150", "Original split at fuel 10 and node 150150",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 149890, 149981, 150064, 150149. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-74801-148953", "context_13_74801_148953", "Context at depth 13, code 74801, node 148953",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 74801 and original node 148953, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-74848-150167", "context_13_74848_150167", "Context at depth 13, code 74848, node 150167",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 74848 and original node 150167, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
