using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1095Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1095.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1095",
        H("Original frontier context coverage 1095"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52564", "selected_cut_52564", "Selected cut at depth 9, code 18157, node 1536591",
                "At remaining fuel 12 and original index 1536591, selection on the full partial prefix of depth 9 and code 18157 returns the complete row with depth 9, base-four code 18157, original node 1536591, kind 2, reserved field 0, 2601 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52609", "selected_cut_52609", "Selected cut at depth 8, code 4618, node 979897",
                "At remaining fuel 13 and original index 979897, selection on the full partial prefix of depth 8 and code 4618 returns the complete row with depth 8, base-four code 4618, original node 979897, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16777216. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-18156-1536390", "unmarked_context_9_18156_1536390", "Unmarked parent at depth 9, code 18156",
                "The frontier Boolean is false at remaining fuel 12, original node 1536390, the whole prefixCache at depth 9 and code 18156, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-4617-1539727", "unmarked_context_8_4617_1539727", "Unmarked parent at depth 8, code 4617",
                "The frontier Boolean is false at remaining fuel 13, original node 1539727, the whole prefixCache at depth 8 and code 4617, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-18156-1536390", "node_context_9_18156_1536390", "Original split at fuel 12 and node 1536390",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1536263, 1536293, 1536389. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-4617-1539727", "node_context_8_4617_1539727", "Original split at fuel 13 and node 1539727",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1539448, 1539681, 33466, 1539726. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-18156-1536390", "context_9_18156_1536390", "Context at depth 9, code 18156, node 1536390",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 18156 and original node 1536390, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_72624_1468246, context_10_72625_1536263, context_10_72626_1536293, context_10_72627_1536389.", DescribeRole.Theorem),
            Node("context-8-4618-979897", "context_8_4618_979897", "Context at depth 8, code 4618, node 979897",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 4618 and original node 979897, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
