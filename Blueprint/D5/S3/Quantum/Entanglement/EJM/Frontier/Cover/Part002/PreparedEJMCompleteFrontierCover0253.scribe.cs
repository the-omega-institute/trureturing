using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0253Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0253.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0253",
        H("Original frontier context coverage 0253"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12148", "selected_cut_12148", "Selected cut at depth 13, code 103927, node 322406",
                "At remaining fuel 8 and original index 322406, selection on the full partial prefix of depth 13 and code 103927 returns the complete row with depth 13, base-four code 103927, original node 322406, kind 2, reserved field 0, 1393 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12194", "selected_cut_12194", "Selected cut at depth 12, code 26027, node 323610",
                "At remaining fuel 9 and original index 323610, selection on the full partial prefix of depth 12 and code 26027 returns the complete row with depth 12, base-four code 26027, original node 323610, kind 2, reserved field 0, 1601 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25981-322407", "unmarked_context_12_25981_322407", "Unmarked parent at depth 12, code 25981",
                "The frontier Boolean is false at remaining fuel 9, original node 322407, the whole prefixCache at depth 12 and code 25981, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6506-323611", "unmarked_context_11_6506_323611", "Unmarked parent at depth 11, code 6506",
                "The frontier Boolean is false at remaining fuel 10, original node 323611, the whole prefixCache at depth 11 and code 6506, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25981-322407", "node_context_12_25981_322407", "Original split at fuel 9 and node 322407",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 322353, 322389, 322406. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6506-323611", "node_context_11_6506_323611", "Original split at fuel 10 and node 323611",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 323558, 323573, 323591, 323610. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-103927-322406", "context_13_103927_322406", "Context at depth 13, code 103927, node 322406",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 103927 and original node 322406, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-6506-323611", "context_11_6506_323611", "Context at depth 11, code 6506, node 323611",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6506 and original node 323611, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_26024_323558, context_12_26025_323573, context_12_26026_323591, context_12_26027_323610.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
