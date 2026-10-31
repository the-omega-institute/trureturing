using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0322Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0322.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0322",
        H("Original frontier context coverage 0322"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15459", "selected_cut_15459", "Selected cut at depth 12, code 27741, node 320864",
                "At remaining fuel 9 and original index 320864, selection on the full partial prefix of depth 12 and code 27741 returns the complete row with depth 12, base-four code 27741, original node 320864, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15506", "selected_cut_15506", "Selected cut at depth 13, code 111044, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 111044 returns the complete row with depth 13, base-four code 111044, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27742-395939", "unmarked_context_12_27742_395939", "Unmarked parent at depth 12, code 27742",
                "The frontier Boolean is false at remaining fuel 9, original node 395939, the whole prefixCache at depth 12 and code 27742, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27760-396910", "unmarked_context_12_27760_396910", "Unmarked parent at depth 12, code 27760",
                "The frontier Boolean is false at remaining fuel 9, original node 396910, the whole prefixCache at depth 12 and code 27760, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27742-395939", "node_context_12_27742_395939", "Original split at fuel 9 and node 395939",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 395907, 395932, 395938. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27760-396910", "node_context_12_27760_396910", "Original split at fuel 9 and node 396910",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 396853, 396904, 396909. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-27741-320864", "context_12_27741_320864", "Context at depth 12, code 27741, node 320864",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27741 and original node 320864, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-111044-3444", "context_13_111044_3444", "Context at depth 13, code 111044, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111044 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
