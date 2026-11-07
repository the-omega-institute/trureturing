using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0473Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0473.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0473",
        H("Original frontier context coverage 0473"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22706", "selected_cut_22706", "Selected cut at depth 12, code 75848, node 576536",
                "At remaining fuel 9 and original index 576536, selection on the full partial prefix of depth 12 and code 75848 returns the complete row with depth 12, base-four code 75848, original node 576536, kind 2, reserved field 0, 2753 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22754", "selected_cut_22754", "Selected cut at depth 12, code 75887, node 578115",
                "At remaining fuel 9 and original index 578115, selection on the full partial prefix of depth 12 and code 75887 returns the complete row with depth 12, base-four code 75887, original node 578115, kind 2, reserved field 0, 2913 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18962-576660", "unmarked_context_11_18962_576660", "Unmarked parent at depth 11, code 18962",
                "The frontier Boolean is false at remaining fuel 10, original node 576660, the whole prefixCache at depth 11 and code 18962, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18971-578116", "unmarked_context_11_18971_578116", "Unmarked parent at depth 11, code 18971",
                "The frontier Boolean is false at remaining fuel 10, original node 578116, the whole prefixCache at depth 11 and code 18971, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18962-576660", "node_context_11_18962_576660", "Original split at fuel 10 and node 576660",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 576536, 576581, 576622, 576659. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18971-578116", "node_context_11_18971_578116", "Original split at fuel 10 and node 578116",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 578016, 578047, 578082, 578115. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75848-576536", "context_12_75848_576536", "Context at depth 12, code 75848, node 576536",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75848 and original node 576536, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-18971-578116", "context_11_18971_578116", "Context at depth 11, code 18971, node 578116",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18971 and original node 578116, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_75884_578016, context_12_75885_578047, context_12_75886_578082, context_12_75887_578115.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
