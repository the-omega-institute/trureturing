using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0556Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0556.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0556",
        H("Original frontier context coverage 0556"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26693", "selected_cut_26693", "Selected cut at depth 13, code 355775, node 674796",
                "At remaining fuel 8 and original index 674796, selection on the full partial prefix of depth 13 and code 355775 returns the complete row with depth 13, base-four code 355775, original node 674796, kind 2, reserved field 0, 1173 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26739", "selected_cut_26739", "Selected cut at depth 12, code 88989, node 676038",
                "At remaining fuel 9 and original index 676038, selection on the full partial prefix of depth 12 and code 88989 returns the complete row with depth 12, base-four code 88989, original node 676038, kind 2, reserved field 0, 1433 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88943-674797", "unmarked_context_12_88943_674797", "Unmarked parent at depth 12, code 88943",
                "The frontier Boolean is false at remaining fuel 9, original node 674797, the whole prefixCache at depth 12 and code 88943, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22246-676004", "unmarked_context_11_22246_676004", "Unmarked parent at depth 11, code 22246",
                "The frontier Boolean is false at remaining fuel 10, original node 676004, the whole prefixCache at depth 11 and code 22246, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88943-674797", "node_context_12_88943_674797", "Original split at fuel 9 and node 674797",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 674763, 674785, 674796. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22246-676004", "node_context_11_22246_676004", "Original split at fuel 10 and node 676004",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 675937, 675956, 675984, 676003. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-355775-674796", "context_13_355775_674796", "Context at depth 13, code 355775, node 674796",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 355775 and original node 674796, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-88989-676038", "context_12_88989_676038", "Context at depth 12, code 88989, node 676038",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88989 and original node 676038, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
