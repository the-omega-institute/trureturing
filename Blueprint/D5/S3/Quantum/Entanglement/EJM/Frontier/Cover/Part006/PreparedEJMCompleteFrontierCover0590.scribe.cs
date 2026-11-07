using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0590Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0590.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0590",
        H("Original frontier context coverage 0590"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28323", "selected_cut_28323", "Selected cut at depth 11, code 23079, node 715768",
                "At remaining fuel 10 and original index 715768, selection on the full partial prefix of depth 11 and code 23079 returns the complete row with depth 11, base-four code 23079, original node 715768, kind 2, reserved field 0, 497 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28370", "selected_cut_28370", "Selected cut at depth 13, code 369734, node 717110",
                "At remaining fuel 8 and original index 717110, selection on the full partial prefix of depth 13 and code 369734 returns the complete row with depth 13, base-four code 369734, original node 717110, kind 2, reserved field 0, 1157 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-5769-715769", "unmarked_context_10_5769_715769", "Unmarked parent at depth 10, code 5769",
                "The frontier Boolean is false at remaining fuel 11, original node 715769, the whole prefixCache at depth 10 and code 5769, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-92432-717055", "unmarked_context_12_92432_717055", "Unmarked parent at depth 12, code 92432",
                "The frontier Boolean is false at remaining fuel 9, original node 717055, the whole prefixCache at depth 12 and code 92432, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-5769-715769", "node_context_10_5769_715769", "Original split at fuel 11 and node 715769",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 715669, 715725, 715756, 715768. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-92432-717055", "node_context_12_92432_717055", "Original split at fuel 9 and node 717055",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 717004, 717028, 717045, 717054. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-23079-715768", "context_11_23079_715768", "Context at depth 11, code 23079, node 715768",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 23079 and original node 715768, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-369734-717110", "context_13_369734_717110", "Context at depth 13, code 369734, node 717110",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 369734 and original node 717110, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
