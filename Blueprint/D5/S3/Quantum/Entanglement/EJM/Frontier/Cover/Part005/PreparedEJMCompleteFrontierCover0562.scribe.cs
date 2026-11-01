using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0562Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0562.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0562",
        H("Original frontier context coverage 0562"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26980", "selected_cut_26980", "Selected cut at depth 13, code 364795, node 681972",
                "At remaining fuel 8 and original index 681972, selection on the full partial prefix of depth 13 and code 364795 returns the complete row with depth 13, base-four code 364795, original node 681972, kind 2, reserved field 0, 797 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27026", "selected_cut_27026", "Selected cut at depth 13, code 364967, node 683643",
                "At remaining fuel 8 and original index 683643, selection on the full partial prefix of depth 13 and code 364967 returns the complete row with depth 13, base-four code 364967, original node 683643, kind 2, reserved field 0, 1305 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91198-681973", "unmarked_context_12_91198_681973", "Unmarked parent at depth 12, code 91198",
                "The frontier Boolean is false at remaining fuel 9, original node 681973, the whole prefixCache at depth 12 and code 91198, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91241-683644", "unmarked_context_12_91241_683644", "Unmarked parent at depth 12, code 91241",
                "The frontier Boolean is false at remaining fuel 9, original node 683644, the whole prefixCache at depth 12 and code 91241, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91198-681973", "node_context_12_91198_681973", "Original split at fuel 9 and node 681973",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 681915, 681947, 681964, 681972. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91241-683644", "node_context_12_91241_683644", "Original split at fuel 9 and node 683644",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 683573, 683609, 683643. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-364795-681972", "context_13_364795_681972", "Context at depth 13, code 364795, node 681972",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 364795 and original node 681972, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-91241-683644", "context_12_91241_683644", "Context at depth 12, code 91241, node 683644",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91241 and original node 683644, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_364964_3444, context_13_364965_683573, context_13_364966_683609, context_13_364967_683643.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
