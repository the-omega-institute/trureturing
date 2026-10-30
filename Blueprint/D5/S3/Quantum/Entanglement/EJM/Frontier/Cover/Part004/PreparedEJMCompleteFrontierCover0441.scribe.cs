using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0441Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0441.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0441",
        H("Original frontier context coverage 0441"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21171", "selected_cut_21171", "Selected cut at depth 13, code 299322, node 541847",
                "At remaining fuel 8 and original index 541847, selection on the full partial prefix of depth 13 and code 299322 returns the complete row with depth 13, base-four code 299322, original node 541847, kind 2, reserved field 0, 1457 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21218", "selected_cut_21218", "Selected cut at depth 13, code 299417, node 542731",
                "At remaining fuel 8 and original index 542731, selection on the full partial prefix of depth 13 and code 299417 returns the complete row with depth 13, base-four code 299417, original node 542731, kind 2, reserved field 0, 1389 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-74830-541858", "unmarked_context_12_74830_541858", "Unmarked parent at depth 12, code 74830",
                "The frontier Boolean is false at remaining fuel 9, original node 541858, the whole prefixCache at depth 12 and code 74830, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18712-542613", "unmarked_context_11_18712_542613", "Unmarked parent at depth 11, code 18712",
                "The frontier Boolean is false at remaining fuel 10, original node 542613, the whole prefixCache at depth 11 and code 18712, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-74830-541858", "node_context_12_74830_541858", "Original split at fuel 9 and node 541858",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 541832, 541847, 541857. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18712-542613", "node_context_11_18712_542613", "Original split at fuel 10 and node 542613",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 542488, 542528, 542573, 542612. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-299322-541847", "context_13_299322_541847", "Context at depth 13, code 299322, node 541847",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 299322 and original node 541847, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-299417-542731", "context_13_299417_542731", "Context at depth 13, code 299417, node 542731",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 299417 and original node 542731, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
