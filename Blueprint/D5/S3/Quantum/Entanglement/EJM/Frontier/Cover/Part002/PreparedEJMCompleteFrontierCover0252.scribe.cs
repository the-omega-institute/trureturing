using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0252Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0252.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0252",
        H("Original frontier context coverage 0252"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12099", "selected_cut_12099", "Selected cut at depth 13, code 103845, node 321392",
                "At remaining fuel 8 and original index 321392, selection on the full partial prefix of depth 13 and code 103845 returns the complete row with depth 13, base-four code 103845, original node 321392, kind 2, reserved field 0, 1285 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12147", "selected_cut_12147", "Selected cut at depth 13, code 103926, node 322389",
                "At remaining fuel 8 and original index 322389, selection on the full partial prefix of depth 13 and code 103926 returns the complete row with depth 13, base-four code 103926, original node 322389, kind 2, reserved field 0, 2897 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25961-321457", "unmarked_context_12_25961_321457", "Unmarked parent at depth 12, code 25961",
                "The frontier Boolean is false at remaining fuel 9, original node 321457, the whole prefixCache at depth 12 and code 25961, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6494-322320", "unmarked_context_11_6494_322320", "Unmarked parent at depth 11, code 6494",
                "The frontier Boolean is false at remaining fuel 10, original node 322320, the whole prefixCache at depth 11 and code 6494, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25961-321457", "node_context_12_25961_321457", "Original split at fuel 9 and node 321457",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 321392, 321429, 321456. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6494-322320", "node_context_11_6494_322320", "Original split at fuel 10 and node 322320",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 322161, 322235, 322277, 322319. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-103845-321392", "context_13_103845_321392", "Context at depth 13, code 103845, node 321392",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 103845 and original node 321392, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-103926-322389", "context_13_103926_322389", "Context at depth 13, code 103926, node 322389",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 103926 and original node 322389, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
