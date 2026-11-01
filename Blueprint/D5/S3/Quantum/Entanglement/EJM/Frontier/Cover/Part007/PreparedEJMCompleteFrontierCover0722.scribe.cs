using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0722Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0722.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0722",
        H("Original frontier context coverage 0722"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34658", "selected_cut_34658", "Selected cut at depth 12, code 281360, node 106538",
                "At remaining fuel 9 and original index 106538, selection on the full partial prefix of depth 12 and code 281360 returns the complete row with depth 12, base-four code 281360, original node 106538, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34706", "selected_cut_34706", "Selected cut at depth 11, code 70367, node 109216",
                "At remaining fuel 10 and original index 109216, selection on the full partial prefix of depth 11 and code 70367 returns the complete row with depth 11, base-four code 70367, original node 109216, kind 2, reserved field 0, 5 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-70340-904021", "unmarked_context_11_70340_904021", "Unmarked parent at depth 11, code 70340",
                "The frontier Boolean is false at remaining fuel 10, original node 904021, the whole prefixCache at depth 11 and code 70340, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-17591-905681", "unmarked_context_10_17591_905681", "Unmarked parent at depth 10, code 17591",
                "The frontier Boolean is false at remaining fuel 11, original node 905681, the whole prefixCache at depth 10 and code 17591, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-70340-904021", "node_context_11_70340_904021", "Original split at fuel 10 and node 904021",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 106538, 903869, 903951, 904020. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-17591-905681", "node_context_10_17591_905681", "Original split at fuel 11 and node 905681",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 905613, 905634, 905680, 109216. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-281360-106538", "context_12_281360_106538", "Context at depth 12, code 281360, node 106538",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 281360 and original node 106538, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-17591-905681", "context_10_17591_905681", "Context at depth 10, code 17591, node 905681",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 17591 and original node 905681, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_70364_905613, context_11_70365_905634, context_11_70366_905680, context_11_70367_109216.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
