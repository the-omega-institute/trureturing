using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0654Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0654.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0654",
        H("Original frontier context coverage 0654"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31395", "selected_cut_31395", "Selected cut at depth 13, code 424002, node 805916",
                "At remaining fuel 8 and original index 805916, selection on the full partial prefix of depth 13 and code 424002 returns the complete row with depth 13, base-four code 424002, original node 805916, kind 2, reserved field 0, 1553 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31443", "selected_cut_31443", "Selected cut at depth 13, code 424053, node 807281",
                "At remaining fuel 8 and original index 807281, selection on the full partial prefix of depth 13 and code 424053 returns the complete row with depth 13, base-four code 424053, original node 807281, kind 2, reserved field 0, 2221 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-106000-805926", "unmarked_context_12_106000_805926", "Unmarked parent at depth 12, code 106000",
                "The frontier Boolean is false at remaining fuel 9, original node 805926, the whole prefixCache at depth 12 and code 106000, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-106012-807207", "unmarked_context_12_106012_807207", "Unmarked parent at depth 12, code 106012",
                "The frontier Boolean is false at remaining fuel 9, original node 807207, the whole prefixCache at depth 12 and code 106012, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-106000-805926", "node_context_12_106000_805926", "Original split at fuel 9 and node 805926",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 805863, 805892, 805916, 805925. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-106012-807207", "node_context_12_106012_807207", "Original split at fuel 9 and node 807207",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 807145, 807178, 807198, 807206. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-424002-805916", "context_13_424002_805916", "Context at depth 13, code 424002, node 805916",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424002 and original node 805916, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-424053-807281", "context_13_424053_807281", "Context at depth 13, code 424053, node 807281",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424053 and original node 807281, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
