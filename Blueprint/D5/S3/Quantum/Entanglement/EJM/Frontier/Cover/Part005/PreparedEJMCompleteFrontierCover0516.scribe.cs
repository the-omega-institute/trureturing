using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0516Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0516.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0516",
        H("Original frontier context coverage 0516"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24772", "selected_cut_24772", "Selected cut at depth 12, code 77380, node 625589",
                "At remaining fuel 9 and original index 625589, selection on the full partial prefix of depth 12 and code 77380 returns the complete row with depth 12, base-four code 77380, original node 625589, kind 2, reserved field 0, 3981 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24819", "selected_cut_24819", "Selected cut at depth 13, code 309594, node 626688",
                "At remaining fuel 8 and original index 626688, selection on the full partial prefix of depth 13 and code 309594 returns the complete row with depth 13, base-four code 309594, original node 626688, kind 2, reserved field 0, 1705 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77379-625529", "unmarked_context_12_77379_625529", "Unmarked parent at depth 12, code 77379",
                "The frontier Boolean is false at remaining fuel 9, original node 625529, the whole prefixCache at depth 12 and code 77379, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19348-626543", "unmarked_context_11_19348_626543", "Unmarked parent at depth 11, code 19348",
                "The frontier Boolean is false at remaining fuel 10, original node 626543, the whole prefixCache at depth 11 and code 19348, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77379-625529", "node_context_12_77379_625529", "Original split at fuel 9 and node 625529",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 625491, 625517, 625528. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19348-626543", "node_context_11_19348_626543", "Original split at fuel 10 and node 626543",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 626341, 626404, 626462, 626542. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-77379-625529", "context_12_77379_625529", "Context at depth 12, code 77379, node 625529",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77379 and original node 625529, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_309516_3444, context_13_309517_625491, context_13_309518_625517, context_13_309519_625528.", DescribeRole.Theorem),
            Node("context-13-309594-626688", "context_13_309594_626688", "Context at depth 13, code 309594, node 626688",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 309594 and original node 626688, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
