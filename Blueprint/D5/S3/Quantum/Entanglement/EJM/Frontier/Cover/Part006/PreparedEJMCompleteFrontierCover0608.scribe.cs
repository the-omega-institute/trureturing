using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0608Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0608.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0608",
        H("Original frontier context coverage 0608"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29188", "selected_cut_29188", "Selected cut at depth 12, code 93355, node 737497",
                "At remaining fuel 9 and original index 737497, selection on the full partial prefix of depth 12 and code 93355 returns the complete row with depth 12, base-four code 93355, original node 737497, kind 2, reserved field 0, 1605 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29234", "selected_cut_29234", "Selected cut at depth 13, code 373799, node 738697",
                "At remaining fuel 8 and original index 738697, selection on the full partial prefix of depth 13 and code 373799 returns the complete row with depth 13, base-four code 373799, original node 738697, kind 2, reserved field 0, 1097 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23338-737498", "unmarked_context_11_23338_737498", "Unmarked parent at depth 11, code 23338",
                "The frontier Boolean is false at remaining fuel 10, original node 737498, the whole prefixCache at depth 11 and code 23338, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93449-738698", "unmarked_context_12_93449_738698", "Unmarked parent at depth 12, code 93449",
                "The frontier Boolean is false at remaining fuel 9, original node 738698, the whole prefixCache at depth 12 and code 93449, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23338-737498", "node_context_11_23338_737498", "Original split at fuel 10 and node 737498",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 737433, 737453, 737472, 737497. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93449-738698", "node_context_12_93449_738698", "Original split at fuel 9 and node 738698",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 738561, 738600, 738674, 738697. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93355-737497", "context_12_93355_737497", "Context at depth 12, code 93355, node 737497",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93355 and original node 737497, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93449-738698", "context_12_93449_738698", "Context at depth 12, code 93449, node 738698",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93449 and original node 738698, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_373796_738561, context_13_373797_738600, context_13_373798_738674, context_13_373799_738697.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
