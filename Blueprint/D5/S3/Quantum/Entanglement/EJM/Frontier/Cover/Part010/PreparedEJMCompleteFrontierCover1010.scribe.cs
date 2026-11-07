using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1010Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1010.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1010",
        H("Original frontier context coverage 1010"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48485", "selected_cut_48485", "Selected cut at depth 11, code 94094, node 1360707",
                "At remaining fuel 10 and original index 1360707, selection on the full partial prefix of depth 11 and code 94094 returns the complete row with depth 11, base-four code 94094, original node 1360707, kind 2, reserved field 0, 3621 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48531", "selected_cut_48531", "Selected cut at depth 12, code 376587, node 1362067",
                "At remaining fuel 9 and original index 1362067, selection on the full partial prefix of depth 12 and code 376587 returns the complete row with depth 12, base-four code 376587, original node 1362067, kind 2, reserved field 0, 2849 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-94093-1360647", "unmarked_context_11_94093_1360647", "Unmarked parent at depth 11, code 94093",
                "The frontier Boolean is false at remaining fuel 10, original node 1360647, the whole prefixCache at depth 11 and code 94093, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-94146-1362068", "unmarked_context_11_94146_1362068", "Unmarked parent at depth 11, code 94146",
                "The frontier Boolean is false at remaining fuel 10, original node 1362068, the whole prefixCache at depth 11 and code 94146, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-94093-1360647", "node_context_11_94093_1360647", "Original split at fuel 10 and node 1360647",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1360528, 1360565, 1360606, 1360646. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-94146-1362068", "node_context_11_94146_1362068", "Original split at fuel 10 and node 1362068",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 34034, 1362011, 1362067. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-94093-1360647", "context_11_94093_1360647", "Context at depth 11, code 94093, node 1360647",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 94093 and original node 1360647, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_376372_1360528, context_12_376373_1360565, context_12_376374_1360606, context_12_376375_1360646.", DescribeRole.Theorem),
            Node("context-11-94146-1362068", "context_11_94146_1362068", "Context at depth 11, code 94146, node 1362068",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 94146 and original node 1362068, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_376584_448748, context_12_376585_34034, context_12_376586_1362011, context_12_376587_1362067.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
