using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0136Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0136.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0136",
        H("Original frontier context coverage 0136"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06530", "selected_cut_06530", "Selected cut at depth 12, code 21650, node 194911",
                "At remaining fuel 9 and original index 194911, selection on the full partial prefix of depth 12 and code 21650 returns the complete row with depth 12, base-four code 21650, original node 194911, kind 2, reserved field 0, 1961 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06577", "selected_cut_06577", "Selected cut at depth 13, code 87073, node 196321",
                "At remaining fuel 8 and original index 196321, selection on the full partial prefix of depth 13 and code 87073 returns the complete row with depth 13, base-four code 87073, original node 196321, kind 2, reserved field 0, 3489 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5412-194946", "unmarked_context_11_5412_194946", "Unmarked parent at depth 11, code 5412",
                "The frontier Boolean is false at remaining fuel 10, original node 194946, the whole prefixCache at depth 11 and code 5412, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5441-196239", "unmarked_context_11_5441_196239", "Unmarked parent at depth 11, code 5441",
                "The frontier Boolean is false at remaining fuel 10, original node 196239, the whole prefixCache at depth 11 and code 5441, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5412-194946", "node_context_11_5412_194946", "Original split at fuel 10 and node 194946",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 194844, 194875, 194911, 194945. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5441-196239", "node_context_11_5441_196239", "Original split at fuel 10 and node 196239",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 195949, 196090, 196238, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-21650-194911", "context_12_21650_194911", "Context at depth 12, code 21650, node 194911",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21650 and original node 194911, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-87073-196321", "context_13_87073_196321", "Context at depth 13, code 87073, node 196321",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 87073 and original node 196321, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
