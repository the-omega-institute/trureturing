using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0773Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0773.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0773",
        H("Original frontier context coverage 0773"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37107", "selected_cut_37107", "Selected cut at depth 12, code 299316, node 991383",
                "At remaining fuel 9 and original index 991383, selection on the full partial prefix of depth 12 and code 299316 returns the complete row with depth 12, base-four code 299316, original node 991383, kind 2, reserved field 0, 3441 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37154", "selected_cut_37154", "Selected cut at depth 12, code 299381, node 891951",
                "At remaining fuel 9 and original index 891951, selection on the full partial prefix of depth 12 and code 299381 returns the complete row with depth 12, base-four code 299381, original node 891951, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-74828-991322", "unmarked_context_11_74828_991322", "Unmarked parent at depth 11, code 74828",
                "The frontier Boolean is false at remaining fuel 10, original node 991322, the whole prefixCache at depth 11 and code 74828, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-74844-992626", "unmarked_context_11_74844_992626", "Unmarked parent at depth 11, code 74844",
                "The frontier Boolean is false at remaining fuel 10, original node 992626, the whole prefixCache at depth 11 and code 74844, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-74828-991322", "node_context_11_74828_991322", "Original split at fuel 10 and node 991322",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 991210, 991253, 991281, 991321. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-74844-992626", "node_context_11_74844_992626", "Original split at fuel 10 and node 992626",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 992566, 992587, 992607, 992625. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-74828-991322", "context_11_74828_991322", "Context at depth 11, code 74828, node 991322",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 74828 and original node 991322, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_299312_991210, context_12_299313_991253, context_12_299314_991281, context_12_299315_991321.", DescribeRole.Theorem),
            Node("context-12-299381-891951", "context_12_299381_891951", "Context at depth 12, code 299381, node 891951",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299381 and original node 891951, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
