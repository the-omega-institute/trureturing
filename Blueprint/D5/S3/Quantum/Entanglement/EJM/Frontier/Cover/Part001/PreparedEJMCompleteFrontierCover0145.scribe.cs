using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0145Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0145.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0145",
        H("Original frontier context coverage 0145"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06963", "selected_cut_06963", "Selected cut at depth 13, code 88203, node 205396",
                "At remaining fuel 8 and original index 205396, selection on the full partial prefix of depth 13 and code 88203 returns the complete row with depth 13, base-four code 88203, original node 205396, kind 2, reserved field 0, 801 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07011", "selected_cut_07011", "Selected cut at depth 13, code 88251, node 206228",
                "At remaining fuel 8 and original index 206228, selection on the full partial prefix of depth 13 and code 88251 returns the complete row with depth 13, base-four code 88251, original node 206228, kind 2, reserved field 0, 765 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22050-205397", "unmarked_context_12_22050_205397", "Unmarked parent at depth 12, code 22050",
                "The frontier Boolean is false at remaining fuel 9, original node 205397, the whole prefixCache at depth 12 and code 22050, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22061-206173", "unmarked_context_12_22061_206173", "Unmarked parent at depth 12, code 22061",
                "The frontier Boolean is false at remaining fuel 9, original node 206173, the whole prefixCache at depth 12 and code 22061, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22050-205397", "node_context_12_22050_205397", "Original split at fuel 9 and node 205397",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 205351, 205379, 205390, 205396. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22061-206173", "node_context_12_22061_206173", "Original split at fuel 9 and node 206173",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 206121, 206146, 206166, 206172. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-88203-205396", "context_13_88203_205396", "Context at depth 13, code 88203, node 205396",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88203 and original node 205396, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-88251-206228", "context_13_88251_206228", "Context at depth 13, code 88251, node 206228",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88251 and original node 206228, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
