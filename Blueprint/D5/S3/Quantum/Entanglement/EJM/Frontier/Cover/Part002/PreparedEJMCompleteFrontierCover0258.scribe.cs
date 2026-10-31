using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0258Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0258.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0258",
        H("Original frontier context coverage 0258"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12387", "selected_cut_12387", "Selected cut at depth 13, code 104598, node 327871",
                "At remaining fuel 8 and original index 327871, selection on the full partial prefix of depth 13 and code 104598 returns the complete row with depth 13, base-four code 104598, original node 327871, kind 2, reserved field 0, 1269 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12435", "selected_cut_12435", "Selected cut at depth 13, code 104655, node 328824",
                "At remaining fuel 8 and original index 328824, selection on the full partial prefix of depth 13 and code 104655 returns the complete row with depth 13, base-four code 104655, original node 328824, kind 2, reserved field 0, 921 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26149-327879", "unmarked_context_12_26149_327879", "Unmarked parent at depth 12, code 26149",
                "The frontier Boolean is false at remaining fuel 9, original node 327879, the whole prefixCache at depth 12 and code 26149, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26162-328740", "unmarked_context_12_26162_328740", "Unmarked parent at depth 12, code 26162",
                "The frontier Boolean is false at remaining fuel 9, original node 328740, the whole prefixCache at depth 12 and code 26162, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26149-327879", "node_context_12_26149_327879", "Original split at fuel 9 and node 327879",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 327832, 327857, 327871, 327878. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26162-328740", "node_context_12_26162_328740", "Original split at fuel 9 and node 328740",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 328692, 328719, 328734, 328739. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-104598-327871", "context_13_104598_327871", "Context at depth 13, code 104598, node 327871",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104598 and original node 327871, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-104655-328824", "context_13_104655_328824", "Context at depth 13, code 104655, node 328824",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104655 and original node 328824, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
