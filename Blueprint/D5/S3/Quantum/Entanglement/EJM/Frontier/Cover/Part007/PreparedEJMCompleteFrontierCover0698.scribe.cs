using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0698Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0698.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0698",
        H("Original frontier context coverage 0698"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33508", "selected_cut_33508", "Selected cut at depth 13, code 441421, node 862723",
                "At remaining fuel 8 and original index 862723, selection on the full partial prefix of depth 13 and code 441421 returns the complete row with depth 13, base-four code 441421, original node 862723, kind 2, reserved field 0, 2613 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33555", "selected_cut_33555", "Selected cut at depth 12, code 110367, node 757807",
                "At remaining fuel 9 and original index 757807, selection on the full partial prefix of depth 12 and code 110367 returns the complete row with depth 12, base-four code 110367, original node 757807, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-110355-862777", "unmarked_context_12_110355_862777", "Unmarked parent at depth 12, code 110355",
                "The frontier Boolean is false at remaining fuel 9, original node 862777, the whole prefixCache at depth 12 and code 110355, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27591-864090", "unmarked_context_11_27591_864090", "Unmarked parent at depth 11, code 27591",
                "The frontier Boolean is false at remaining fuel 10, original node 864090, the whole prefixCache at depth 11 and code 27591, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-110355-862777", "node_context_12_110355_862777", "Original split at fuel 9 and node 862777",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 862694, 862723, 862770, 862776. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27591-864090", "node_context_11_27591_864090", "Original split at fuel 10 and node 864090",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 863883, 864000, 864089, 757807. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-441421-862723", "context_13_441421_862723", "Context at depth 13, code 441421, node 862723",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 441421 and original node 862723, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-27591-864090", "context_11_27591_864090", "Context at depth 11, code 27591, node 864090",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27591 and original node 864090, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_110364_863883, context_12_110365_864000, context_12_110366_864089, context_12_110367_757807.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
