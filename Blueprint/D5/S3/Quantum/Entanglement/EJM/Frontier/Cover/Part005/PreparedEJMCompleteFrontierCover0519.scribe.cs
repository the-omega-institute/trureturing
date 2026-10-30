using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0519Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0519.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0519",
        H("Original frontier context coverage 0519"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24915", "selected_cut_24915", "Selected cut at depth 12, code 77472, node 629656",
                "At remaining fuel 9 and original index 629656, selection on the full partial prefix of depth 12 and code 77472 returns the complete row with depth 12, base-four code 77472, original node 629656, kind 2, reserved field 0, 1485 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24962", "selected_cut_24962", "Selected cut at depth 12, code 77576, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 77576 returns the complete row with depth 12, base-four code 77576, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19368-629725", "unmarked_context_11_19368_629725", "Unmarked parent at depth 11, code 19368",
                "The frontier Boolean is false at remaining fuel 10, original node 629725, the whole prefixCache at depth 11 and code 19368, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19393-630821", "unmarked_context_11_19393_630821", "Unmarked parent at depth 11, code 19393",
                "The frontier Boolean is false at remaining fuel 10, original node 630821, the whole prefixCache at depth 11 and code 19393, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19368-629725", "node_context_11_19368_629725", "Original split at fuel 10 and node 629725",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 629656, 629682, 629702, 629724. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19393-630821", "node_context_11_19393_630821", "Original split at fuel 10 and node 630821",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 34034, 630820, 603785. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-77472-629656", "context_12_77472_629656", "Context at depth 12, code 77472, node 629656",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77472 and original node 629656, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-77576-448748", "context_12_77576_448748", "Context at depth 12, code 77576, node 448748",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77576 and original node 448748, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
