using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0302Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0302.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0302",
        H("Original frontier context coverage 0302"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14500", "selected_cut_14500", "Selected cut at depth 13, code 108919, node 373952",
                "At remaining fuel 8 and original index 373952, selection on the full partial prefix of depth 13 and code 108919 returns the complete row with depth 13, base-four code 108919, original node 373952, kind 2, reserved field 0, 1101 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14547", "selected_cut_14547", "Selected cut at depth 12, code 27261, node 375230",
                "At remaining fuel 9 and original index 375230, selection on the full partial prefix of depth 12 and code 27261 returns the complete row with depth 12, base-four code 27261, original node 375230, kind 2, reserved field 0, 3369 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27229-373953", "unmarked_context_12_27229_373953", "Unmarked parent at depth 12, code 27229",
                "The frontier Boolean is false at remaining fuel 9, original node 373953, the whole prefixCache at depth 12 and code 27229, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6814-375160", "unmarked_context_11_6814_375160", "Unmarked parent at depth 11, code 6814",
                "The frontier Boolean is false at remaining fuel 10, original node 375160, the whole prefixCache at depth 11 and code 6814, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27229-373953", "node_context_12_27229_373953", "Original split at fuel 9 and node 373953",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 373915, 373939, 373952. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6814-375160", "node_context_11_6814_375160", "Original split at fuel 10 and node 375160",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 375026, 375061, 375121, 375159. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-108919-373952", "context_13_108919_373952", "Context at depth 13, code 108919, node 373952",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 108919 and original node 373952, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27261-375230", "context_12_27261_375230", "Context at depth 12, code 27261, node 375230",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27261 and original node 375230, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
