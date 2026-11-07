using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0104Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0104.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0104",
        H("Original frontier context coverage 0104"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04995", "selected_cut_04995", "Selected cut at depth 12, code 18804, node 156245",
                "At remaining fuel 9 and original index 156245, selection on the full partial prefix of depth 12 and code 18804 returns the complete row with depth 12, base-four code 18804, original node 156245, kind 2, reserved field 0, 3273 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05042", "selected_cut_05042", "Selected cut at depth 12, code 18845, node 157426",
                "At remaining fuel 9 and original index 157426, selection on the full partial prefix of depth 12 and code 18845 returns the complete row with depth 12, base-four code 18845, original node 157426, kind 2, reserved field 0, 1873 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-4700-156207", "unmarked_context_11_4700_156207", "Unmarked parent at depth 11, code 4700",
                "The frontier Boolean is false at remaining fuel 10, original node 156207, the whole prefixCache at depth 11 and code 4700, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4710-157380", "unmarked_context_11_4710_157380", "Unmarked parent at depth 11, code 4710",
                "The frontier Boolean is false at remaining fuel 10, original node 157380, the whole prefixCache at depth 11 and code 4710, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-4700-156207", "node_context_11_4700_156207", "Original split at fuel 10 and node 156207",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 156061, 156112, 156155, 156206. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4710-157380", "node_context_11_4710_157380", "Original split at fuel 10 and node 157380",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 157309, 157331, 157353, 157379. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-4700-156207", "context_11_4700_156207", "Context at depth 11, code 4700, node 156207",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 4700 and original node 156207, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_18800_156061, context_12_18801_156112, context_12_18802_156155, context_12_18803_156206.", DescribeRole.Theorem),
            Node("context-12-18845-157426", "context_12_18845_157426", "Context at depth 12, code 18845, node 157426",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18845 and original node 157426, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
