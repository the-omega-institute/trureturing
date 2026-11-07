using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0667Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0667.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0667",
        H("Original frontier context coverage 0667"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32020", "selected_cut_32020", "Selected cut at depth 13, code 431224, node 822762",
                "At remaining fuel 8 and original index 822762, selection on the full partial prefix of depth 13 and code 431224 returns the complete row with depth 13, base-four code 431224, original node 822762, kind 2, reserved field 0, 1613 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32067", "selected_cut_32067", "Selected cut at depth 13, code 431274, node 823840",
                "At remaining fuel 8 and original index 823840, selection on the full partial prefix of depth 13 and code 431274 returns the complete row with depth 13, base-four code 431274, original node 823840, kind 2, reserved field 0, 1237 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-107805-822737", "unmarked_context_12_107805_822737", "Unmarked parent at depth 12, code 107805",
                "The frontier Boolean is false at remaining fuel 9, original node 822737, the whole prefixCache at depth 12 and code 107805, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-107817-823786", "unmarked_context_12_107817_823786", "Unmarked parent at depth 12, code 107817",
                "The frontier Boolean is false at remaining fuel 9, original node 823786, the whole prefixCache at depth 12 and code 107817, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-107805-822737", "node_context_12_107805_822737", "Original split at fuel 9 and node 822737",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 822668, 822705, 822729, 822736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-107817-823786", "node_context_12_107817_823786", "Original split at fuel 9 and node 823786",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 823725, 823753, 823776, 823785. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-107805-822737", "context_12_107805_822737", "Context at depth 12, code 107805, node 822737",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 107805 and original node 822737, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_431220_822668, context_13_431221_822705, context_13_431222_822729, context_13_431223_822736.", DescribeRole.Theorem),
            Node("context-13-431274-823840", "context_13_431274_823840", "Context at depth 13, code 431274, node 823840",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 431274 and original node 823840, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
