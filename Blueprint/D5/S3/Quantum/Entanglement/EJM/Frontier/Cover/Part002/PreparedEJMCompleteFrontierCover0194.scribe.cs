using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0194Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0194.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0194",
        H("Original frontier context coverage 0194"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09316", "selected_cut_09316", "Selected cut at depth 13, code 93421, node 257419",
                "At remaining fuel 8 and original index 257419, selection on the full partial prefix of depth 13 and code 93421 returns the complete row with depth 13, base-four code 93421, original node 257419, kind 2, reserved field 0, 3181 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09362", "selected_cut_09362", "Selected cut at depth 14, code 373847, node 258452",
                "At remaining fuel 7 and original index 258452, selection on the full partial prefix of depth 14 and code 373847 returns the complete row with depth 14, base-four code 373847, original node 258452, kind 2, reserved field 0, 1005 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23355-257457", "unmarked_context_12_23355_257457", "Unmarked parent at depth 12, code 23355",
                "The frontier Boolean is false at remaining fuel 9, original node 257457, the whole prefixCache at depth 12 and code 23355, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-93461-258453", "unmarked_context_13_93461_258453", "Unmarked parent at depth 13, code 93461",
                "The frontier Boolean is false at remaining fuel 8, original node 258453, the whole prefixCache at depth 13 and code 93461, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23355-257457", "node_context_12_23355_257457", "Original split at fuel 9 and node 257457",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 257381, 257419, 257447, 257456. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-93461-258453", "node_context_13_93461_258453", "Original split at fuel 8 and node 258453",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 258391, 258409, 258436, 258452. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-93421-257419", "context_13_93421_257419", "Context at depth 13, code 93421, node 257419",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93421 and original node 257419, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-93461-258453", "context_13_93461_258453", "Context at depth 13, code 93461, node 258453",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93461 and original node 258453, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_373844_258391, context_14_373845_258409, context_14_373846_258436, context_14_373847_258452.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
