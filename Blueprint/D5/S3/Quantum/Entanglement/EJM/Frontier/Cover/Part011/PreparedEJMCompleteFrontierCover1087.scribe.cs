using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1087Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1087.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1087",
        H("Original frontier context coverage 1087"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52179", "selected_cut_52179", "Selected cut at depth 11, code 287625, node 1516897",
                "At remaining fuel 10 and original index 1516897, selection on the full partial prefix of depth 11 and code 287625 returns the complete row with depth 11, base-four code 287625, original node 1516897, kind 2, reserved field 0, 1269 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52225", "selected_cut_52225", "Selected cut at depth 11, code 288772, node 1518654",
                "At remaining fuel 10 and original index 1518654, selection on the full partial prefix of depth 11 and code 288772 returns the complete row with depth 11, base-four code 288772, original node 1518654, kind 2, reserved field 0, 1225 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-71906-1516928", "unmarked_context_10_71906_1516928", "Unmarked parent at depth 10, code 71906",
                "The frontier Boolean is false at remaining fuel 11, original node 1516928, the whole prefixCache at depth 10 and code 71906, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-6-280-1518610", "unmarked_context_6_280_1518610", "Unmarked parent at depth 6, code 280",
                "The frontier Boolean is false at remaining fuel 15, original node 1518610, the whole prefixCache at depth 6 and code 280, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-71906-1516928", "node_context_10_71906_1516928", "Original split at fuel 11 and node 1516928",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1516867, 1516897, 1468743, 1516927. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-6-280-1518610", "node_context_6_280_1518610", "Original split at fuel 15 and node 1518610",
                "The complete original decoder output is the split at coordinate 6, with value children 0 through 3 respectively at original indices 1510459, 1510460, 1514617, 1518609. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-287625-1516897", "context_11_287625_1516897", "Context at depth 11, code 287625, node 1516897",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 287625 and original node 1516897, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-288772-1518654", "context_11_288772_1518654", "Context at depth 11, code 288772, node 1518654",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 288772 and original node 1518654, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
