using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0585Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0585.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0585",
        H("Original frontier context coverage 0585"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28084", "selected_cut_28084", "Selected cut at depth 12, code 92044, node 709309",
                "At remaining fuel 9 and original index 709309, selection on the full partial prefix of depth 12 and code 92044 returns the complete row with depth 12, base-four code 92044, original node 709309, kind 2, reserved field 0, 1749 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28131", "selected_cut_28131", "Selected cut at depth 12, code 92091, node 710184",
                "At remaining fuel 9 and original index 710184, selection on the full partial prefix of depth 12 and code 92091 returns the complete row with depth 12, base-four code 92091, original node 710184, kind 2, reserved field 0, 1049 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23010-709292", "unmarked_context_11_23010_709292", "Unmarked parent at depth 11, code 23010",
                "The frontier Boolean is false at remaining fuel 10, original node 709292, the whole prefixCache at depth 11 and code 23010, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23022-710185", "unmarked_context_11_23022_710185", "Unmarked parent at depth 11, code 23022",
                "The frontier Boolean is false at remaining fuel 10, original node 710185, the whole prefixCache at depth 11 and code 23022, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23010-709292", "node_context_11_23010_709292", "Original split at fuel 10 and node 709292",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 709196, 709228, 709255, 709291. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23022-710185", "node_context_11_23022_710185", "Original split at fuel 10 and node 710185",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 710139, 710158, 710170, 710184. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-23010-709292", "context_11_23010_709292", "Context at depth 11, code 23010, node 709292",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 23010 and original node 709292, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_92040_709196, context_12_92041_709228, context_12_92042_709255, context_12_92043_709291.", DescribeRole.Theorem),
            Node("context-11-23022-710185", "context_11_23022_710185", "Context at depth 11, code 23022, node 710185",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 23022 and original node 710185, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_92088_710139, context_12_92089_710158, context_12_92090_710170, context_12_92091_710184.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
