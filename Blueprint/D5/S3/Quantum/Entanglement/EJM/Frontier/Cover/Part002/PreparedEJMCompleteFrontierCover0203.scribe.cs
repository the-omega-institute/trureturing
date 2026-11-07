using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0203Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0203.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0203",
        H("Original frontier context coverage 0203"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09746", "selected_cut_09746", "Selected cut at depth 13, code 98597, node 269090",
                "At remaining fuel 8 and original index 269090, selection on the full partial prefix of depth 13 and code 98597 returns the complete row with depth 13, base-four code 98597, original node 269090, kind 2, reserved field 0, 2685 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09793", "selected_cut_09793", "Selected cut at depth 13, code 98671, node 269950",
                "At remaining fuel 8 and original index 269950, selection on the full partial prefix of depth 13 and code 98671 returns the complete row with depth 13, base-four code 98671, original node 269950, kind 2, reserved field 0, 1069 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-24649-269123", "unmarked_context_12_24649_269123", "Unmarked parent at depth 12, code 24649",
                "The frontier Boolean is false at remaining fuel 9, original node 269123, the whole prefixCache at depth 12 and code 24649, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6166-269952", "unmarked_context_11_6166_269952", "Unmarked parent at depth 11, code 6166",
                "The frontier Boolean is false at remaining fuel 10, original node 269952, the whole prefixCache at depth 11 and code 6166, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-24649-269123", "node_context_12_24649_269123", "Original split at fuel 9 and node 269123",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 269090, 269114, 269122. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6166-269952", "node_context_11_6166_269952", "Original split at fuel 10 and node 269952",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 269782, 269861, 269904, 269951. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-98597-269090", "context_13_98597_269090", "Context at depth 13, code 98597, node 269090",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 98597 and original node 269090, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-6166-269952", "context_11_6166_269952", "Context at depth 11, code 6166, node 269952",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6166 and original node 269952, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_24664_269782, context_12_24665_269861, context_12_24666_269904, context_12_24667_269951.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
