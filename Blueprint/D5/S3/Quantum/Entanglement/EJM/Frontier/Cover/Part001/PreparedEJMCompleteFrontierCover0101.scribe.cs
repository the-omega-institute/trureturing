using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0101Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0101.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0101",
        H("Original frontier context coverage 0101"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04850", "selected_cut_04850", "Selected cut at depth 13, code 75041, node 153850",
                "At remaining fuel 8 and original index 153850, selection on the full partial prefix of depth 13 and code 75041 returns the complete row with depth 13, base-four code 75041, original node 153850, kind 2, reserved field 0, 2313 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04897", "selected_cut_04897", "Selected cut at depth 12, code 18772, node 154580",
                "At remaining fuel 9 and original index 154580, selection on the full partial prefix of depth 12 and code 18772 returns the complete row with depth 12, base-four code 18772, original node 154580, kind 2, reserved field 0, 3621 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18760-153879", "unmarked_context_12_18760_153879", "Unmarked parent at depth 12, code 18760",
                "The frontier Boolean is false at remaining fuel 9, original node 153879, the whole prefixCache at depth 12 and code 18760, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4692-154536", "unmarked_context_11_4692_154536", "Unmarked parent at depth 11, code 4692",
                "The frontier Boolean is false at remaining fuel 10, original node 154536, the whole prefixCache at depth 11 and code 4692, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18760-153879", "node_context_12_18760_153879", "Original split at fuel 9 and node 153879",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 153850, 153868, 153878. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4692-154536", "node_context_11_4692_154536", "Original split at fuel 10 and node 154536",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 154338, 154406, 154475, 154535. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-75041-153850", "context_13_75041_153850", "Context at depth 13, code 75041, node 153850",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 75041 and original node 153850, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-18772-154580", "context_12_18772_154580", "Context at depth 12, code 18772, node 154580",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18772 and original node 154580, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
