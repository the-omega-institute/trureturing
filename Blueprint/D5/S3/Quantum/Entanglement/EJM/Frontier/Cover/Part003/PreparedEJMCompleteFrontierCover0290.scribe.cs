using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0290Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0290.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0290",
        H("Original frontier context coverage 0290"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13923", "selected_cut_13923", "Selected cut at depth 12, code 26949, node 126884",
                "At remaining fuel 9 and original index 126884, selection on the full partial prefix of depth 12 and code 26949 returns the complete row with depth 12, base-four code 26949, original node 126884, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13970", "selected_cut_13970", "Selected cut at depth 13, code 107849, node 363582",
                "At remaining fuel 8 and original index 363582, selection on the full partial prefix of depth 13 and code 107849 returns the complete row with depth 13, base-four code 107849, original node 363582, kind 2, reserved field 0, 1905 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26948-362989", "unmarked_context_12_26948_362989", "Unmarked parent at depth 12, code 26948",
                "The frontier Boolean is false at remaining fuel 9, original node 362989, the whole prefixCache at depth 12 and code 26948, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26960-363562", "unmarked_context_12_26960_363562", "Unmarked parent at depth 12, code 26960",
                "The frontier Boolean is false at remaining fuel 9, original node 363562, the whole prefixCache at depth 12 and code 26960, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26948-362989", "node_context_12_26948_362989", "Original split at fuel 9 and node 362989",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 362966, 362984, 362988. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26960-363562", "node_context_12_26960_363562", "Original split at fuel 9 and node 363562",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 363537, 363553, 363561. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26948-362989", "context_12_26948_362989", "Context at depth 12, code 26948, node 362989",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26948 and original node 362989, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_107792_3444, context_13_107793_362966, context_13_107794_362984, context_13_107795_362988.", DescribeRole.Theorem),
            Node("context-13-107849-363582", "context_13_107849_363582", "Context at depth 13, code 107849, node 363582",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 107849 and original node 363582, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
