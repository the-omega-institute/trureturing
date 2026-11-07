using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0420Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0420.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0420",
        H("Original frontier context coverage 0420"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20164", "selected_cut_20164", "Selected cut at depth 12, code 72574, node 516119",
                "At remaining fuel 9 and original index 516119, selection on the full partial prefix of depth 12 and code 72574 returns the complete row with depth 12, base-four code 72574, original node 516119, kind 2, reserved field 0, 3049 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20210", "selected_cut_20210", "Selected cut at depth 12, code 72623, node 517217",
                "At remaining fuel 9 and original index 517217, selection on the full partial prefix of depth 12 and code 72623 returns the complete row with depth 12, base-four code 72623, original node 517217, kind 2, reserved field 0, 1873 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18143-516120", "unmarked_context_11_18143_516120", "Unmarked parent at depth 11, code 18143",
                "The frontier Boolean is false at remaining fuel 10, original node 516120, the whole prefixCache at depth 11 and code 18143, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4538-517219", "unmarked_context_10_4538_517219", "Unmarked parent at depth 10, code 4538",
                "The frontier Boolean is false at remaining fuel 11, original node 517219, the whole prefixCache at depth 10 and code 4538, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18143-516120", "node_context_11_18143_516120", "Original split at fuel 10 and node 516120",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 516051, 516084, 516119, 512556. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4538-517219", "node_context_10_4538_517219", "Original split at fuel 11 and node 517219",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 517074, 517146, 479708, 517218. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-72574-516119", "context_12_72574_516119", "Context at depth 12, code 72574, node 516119",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72574 and original node 516119, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-4538-517219", "context_10_4538_517219", "Context at depth 10, code 4538, node 517219",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4538 and original node 517219, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_18152_517074, context_11_18153_517146, context_11_18154_479708, context_11_18155_517218.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
