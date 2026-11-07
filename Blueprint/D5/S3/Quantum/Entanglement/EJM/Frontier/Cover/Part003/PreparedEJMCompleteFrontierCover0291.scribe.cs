using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0291Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0291.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0291",
        H("Original frontier context coverage 0291"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13971", "selected_cut_13971", "Selected cut at depth 13, code 107850, node 363603",
                "At remaining fuel 8 and original index 363603, selection on the full partial prefix of depth 13 and code 107850 returns the complete row with depth 13, base-four code 107850, original node 363603, kind 2, reserved field 0, 1961 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14019", "selected_cut_14019", "Selected cut at depth 13, code 107919, node 364255",
                "At remaining fuel 8 and original index 364255, selection on the full partial prefix of depth 13 and code 107919 returns the complete row with depth 13, base-four code 107919, original node 364255, kind 2, reserved field 0, 1057 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26962-363613", "unmarked_context_12_26962_363613", "Unmarked parent at depth 12, code 26962",
                "The frontier Boolean is false at remaining fuel 9, original node 363613, the whole prefixCache at depth 12 and code 26962, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26978-364209", "unmarked_context_12_26978_364209", "Unmarked parent at depth 12, code 26978",
                "The frontier Boolean is false at remaining fuel 9, original node 364209, the whole prefixCache at depth 12 and code 26978, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26962-363613", "node_context_12_26962_363613", "Original split at fuel 9 and node 363613",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 363582, 363603, 363612. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26978-364209", "node_context_12_26978_364209", "Original split at fuel 9 and node 364209",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 364176, 364199, 364208. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-107850-363603", "context_13_107850_363603", "Context at depth 13, code 107850, node 363603",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 107850 and original node 363603, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-107919-364255", "context_13_107919_364255", "Context at depth 13, code 107919, node 364255",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 107919 and original node 364255, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
