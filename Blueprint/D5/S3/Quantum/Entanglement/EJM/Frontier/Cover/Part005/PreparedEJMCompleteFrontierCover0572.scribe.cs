using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0572Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0572.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0572",
        H("Original frontier context coverage 0572"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27459", "selected_cut_27459", "Selected cut at depth 14, code 1466529, node 694160",
                "At remaining fuel 7 and original index 694160, selection on the full partial prefix of depth 14 and code 1466529 returns the complete row with depth 14, base-four code 1466529, original node 694160, kind 2, reserved field 0, 1293 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27506", "selected_cut_27506", "Selected cut at depth 13, code 366683, node 695447",
                "At remaining fuel 8 and original index 695447, selection on the full partial prefix of depth 13 and code 366683 returns the complete row with depth 13, base-four code 366683, original node 695447, kind 2, reserved field 0, 1177 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-366632-694206", "unmarked_context_13_366632_694206", "Unmarked parent at depth 13, code 366632",
                "The frontier Boolean is false at remaining fuel 8, original node 694206, the whole prefixCache at depth 13 and code 366632, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91670-695448", "unmarked_context_12_91670_695448", "Unmarked parent at depth 12, code 91670",
                "The frontier Boolean is false at remaining fuel 9, original node 695448, the whole prefixCache at depth 12 and code 91670, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-366632-694206", "node_context_13_366632_694206", "Original split at fuel 8 and node 694206",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 694130, 694160, 694170, 694205. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91670-695448", "node_context_12_91670_695448", "Original split at fuel 9 and node 695448",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 695383, 695419, 695437, 695447. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-1466529-694160", "context_14_1466529_694160", "Context at depth 14, code 1466529, node 694160",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 1466529 and original node 694160, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-91670-695448", "context_12_91670_695448", "Context at depth 12, code 91670, node 695448",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91670 and original node 695448, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_366680_695383, context_13_366681_695419, context_13_366682_695437, context_13_366683_695447.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
