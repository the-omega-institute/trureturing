using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0384Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0384.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0384",
        H("Original frontier context coverage 0384"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18435", "selected_cut_18435", "Selected cut at depth 12, code 71700, node 449505",
                "At remaining fuel 9 and original index 449505, selection on the full partial prefix of depth 12 and code 71700 returns the complete row with depth 12, base-four code 71700, original node 449505, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18481", "selected_cut_18481", "Selected cut at depth 13, code 286852, node 473526",
                "At remaining fuel 8 and original index 473526, selection on the full partial prefix of depth 13 and code 286852 returns the complete row with depth 13, base-four code 286852, original node 473526, kind 2, reserved field 0, 1049 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71699-472200", "unmarked_context_12_71699_472200", "Unmarked parent at depth 12, code 71699",
                "The frontier Boolean is false at remaining fuel 9, original node 472200, the whole prefixCache at depth 12 and code 71699, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4481-473506", "unmarked_context_10_4481_473506", "Unmarked parent at depth 10, code 4481",
                "The frontier Boolean is false at remaining fuel 11, original node 473506, the whole prefixCache at depth 10 and code 4481, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71699-472200", "node_context_12_71699_472200", "Original split at fuel 9 and node 472200",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 472132, 472169, 472193, 472199. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4481-473506", "node_context_10_4481_473506", "Original split at fuel 11 and node 473506",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 472201, 472604, 473063, 473505. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-71699-472200", "context_12_71699_472200", "Context at depth 12, code 71699, node 472200",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71699 and original node 472200, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_286796_472132, context_13_286797_472169, context_13_286798_472193, context_13_286799_472199.", DescribeRole.Theorem),
            Node("context-13-286852-473526", "context_13_286852_473526", "Context at depth 13, code 286852, node 473526",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 286852 and original node 473526, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
