using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0155Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0155.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0155",
        H("Original frontier context coverage 0155"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07442", "selected_cut_07442", "Selected cut at depth 13, code 90209, node 216237",
                "At remaining fuel 8 and original index 216237, selection on the full partial prefix of depth 13 and code 90209 returns the complete row with depth 13, base-four code 90209, original node 216237, kind 2, reserved field 0, 2377 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07489", "selected_cut_07489", "Selected cut at depth 13, code 90256, node 217224",
                "At remaining fuel 8 and original index 217224, selection on the full partial prefix of depth 13 and code 90256 returns the complete row with depth 13, base-four code 90256, original node 217224, kind 2, reserved field 0, 753 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22552-216266", "unmarked_context_12_22552_216266", "Unmarked parent at depth 12, code 22552",
                "The frontier Boolean is false at remaining fuel 9, original node 216266, the whole prefixCache at depth 12 and code 22552, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5640-217213", "unmarked_context_11_5640_217213", "Unmarked parent at depth 11, code 5640",
                "The frontier Boolean is false at remaining fuel 10, original node 217213, the whole prefixCache at depth 11 and code 5640, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22552-216266", "node_context_12_22552_216266", "Original split at fuel 9 and node 216266",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 216201, 216237, 216256, 216265. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5640-217213", "node_context_11_5640_217213", "Original split at fuel 10 and node 217213",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 217004, 217069, 217146, 217212. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-90209-216237", "context_13_90209_216237", "Context at depth 13, code 90209, node 216237",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90209 and original node 216237, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-90256-217224", "context_13_90256_217224", "Context at depth 13, code 90256, node 217224",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90256 and original node 217224, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
