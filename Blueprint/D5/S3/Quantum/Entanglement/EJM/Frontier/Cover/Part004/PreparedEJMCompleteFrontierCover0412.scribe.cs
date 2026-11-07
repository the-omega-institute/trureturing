using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0412Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0412.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0412",
        H("Original frontier context coverage 0412"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19779", "selected_cut_19779", "Selected cut at depth 12, code 72345, node 505875",
                "At remaining fuel 9 and original index 505875, selection on the full partial prefix of depth 12 and code 72345 returns the complete row with depth 12, base-four code 72345, original node 505875, kind 2, reserved field 0, 1873 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19826", "selected_cut_19826", "Selected cut at depth 11, code 18107, node 507008",
                "At remaining fuel 10 and original index 507008, selection on the full partial prefix of depth 11 and code 18107 returns the complete row with depth 11, base-four code 18107, original node 507008, kind 2, reserved field 0, 925 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18086-505896", "unmarked_context_11_18086_505896", "Unmarked parent at depth 11, code 18086",
                "The frontier Boolean is false at remaining fuel 10, original node 505896, the whole prefixCache at depth 11 and code 18086, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4526-507009", "unmarked_context_10_4526_507009", "Unmarked parent at depth 10, code 4526",
                "The frontier Boolean is false at remaining fuel 11, original node 507009, the whole prefixCache at depth 10 and code 4526, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18086-505896", "node_context_11_18086_505896", "Original split at fuel 10 and node 505896",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 505840, 505875, 212113, 505895. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4526-507009", "node_context_10_4526_507009", "Original split at fuel 11 and node 507009",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 506967, 506984, 506996, 507008. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-72345-505875", "context_12_72345_505875", "Context at depth 12, code 72345, node 505875",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72345 and original node 505875, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-4526-507009", "context_10_4526_507009", "Context at depth 10, code 4526, node 507009",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4526 and original node 507009, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_18104_506967, context_11_18105_506984, context_11_18106_506996, context_11_18107_507008.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
