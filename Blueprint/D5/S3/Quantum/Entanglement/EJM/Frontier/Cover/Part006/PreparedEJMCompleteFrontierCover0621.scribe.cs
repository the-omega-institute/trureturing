using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0621Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0621.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0621",
        H("Original frontier context coverage 0621"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29812", "selected_cut_29812", "Selected cut at depth 12, code 93790, node 752202",
                "At remaining fuel 9 and original index 752202, selection on the full partial prefix of depth 12 and code 93790 returns the complete row with depth 12, base-four code 93790, original node 752202, kind 2, reserved field 0, 2713 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29859", "selected_cut_29859", "Selected cut at depth 12, code 93834, node 448662",
                "At remaining fuel 9 and original index 448662, selection on the full partial prefix of depth 12 and code 93834 returns the complete row with depth 12, base-four code 93834, original node 448662, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23447-752251", "unmarked_context_11_23447_752251", "Unmarked parent at depth 11, code 23447",
                "The frontier Boolean is false at remaining fuel 10, original node 752251, the whole prefixCache at depth 11 and code 23447, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23457-753637", "unmarked_context_11_23457_753637", "Unmarked parent at depth 11, code 23457",
                "The frontier Boolean is false at remaining fuel 10, original node 753637, the whole prefixCache at depth 11 and code 23457, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23447-752251", "node_context_11_23447_752251", "Original split at fuel 10 and node 752251",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 752161, 642341, 752202, 752250. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23457-753637", "node_context_11_23457_753637", "Original split at fuel 10 and node 753637",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 753562, 753584, 753607, 753636. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93790-752202", "context_12_93790_752202", "Context at depth 12, code 93790, node 752202",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93790 and original node 752202, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93834-448662", "context_12_93834_448662", "Context at depth 12, code 93834, node 448662",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93834 and original node 448662, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
