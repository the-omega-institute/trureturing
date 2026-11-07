using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0390Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0390.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0390",
        H("Original frontier context coverage 0390"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18722", "selected_cut_18722", "Selected cut at depth 12, code 71810, node 478802",
                "At remaining fuel 9 and original index 478802, selection on the full partial prefix of depth 12 and code 71810 returns the complete row with depth 12, base-four code 71810, original node 478802, kind 2, reserved field 0, 2241 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18770", "selected_cut_18770", "Selected cut at depth 12, code 71861, node 479865",
                "At remaining fuel 9 and original index 479865, selection on the full partial prefix of depth 12 and code 71861 returns the complete row with depth 12, base-four code 71861, original node 479865, kind 2, reserved field 0, 1417 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-17952-478834", "unmarked_context_11_17952_478834", "Unmarked parent at depth 11, code 17952",
                "The frontier Boolean is false at remaining fuel 10, original node 478834, the whole prefixCache at depth 11 and code 17952, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-17964-479837", "unmarked_context_11_17964_479837", "Unmarked parent at depth 11, code 17964",
                "The frontier Boolean is false at remaining fuel 10, original node 479837, the whole prefixCache at depth 11 and code 17964, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-17952-478834", "node_context_11_17952_478834", "Original split at fuel 10 and node 478834",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 450982, 478780, 478802, 478833. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-17964-479837", "node_context_11_17964_479837", "Original split at fuel 10 and node 479837",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 479810, 479817, 479827, 479836. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-71810-478802", "context_12_71810_478802", "Context at depth 12, code 71810, node 478802",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71810 and original node 478802, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-71861-479865", "context_12_71861_479865", "Context at depth 12, code 71861, node 479865",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71861 and original node 479865, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
