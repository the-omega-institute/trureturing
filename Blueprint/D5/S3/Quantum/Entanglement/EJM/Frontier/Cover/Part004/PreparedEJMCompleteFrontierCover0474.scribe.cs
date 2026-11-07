using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0474Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0474.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0474",
        H("Original frontier context coverage 0474"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22755", "selected_cut_22755", "Selected cut at depth 13, code 303552, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 303552 returns the complete row with depth 13, base-four code 303552, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22802", "selected_cut_22802", "Selected cut at depth 12, code 75932, node 579487",
                "At remaining fuel 9 and original index 579487, selection on the full partial prefix of depth 12 and code 75932 returns the complete row with depth 12, base-four code 75932, original node 579487, kind 2, reserved field 0, 1737 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-4742-578117", "unmarked_context_10_4742_578117", "Unmarked parent at depth 10, code 4742",
                "The frontier Boolean is false at remaining fuel 11, original node 578117, the whole prefixCache at depth 10 and code 4742, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18982-579466", "unmarked_context_11_18982_579466", "Unmarked parent at depth 11, code 18982",
                "The frontier Boolean is false at remaining fuel 10, original node 579466, the whole prefixCache at depth 11 and code 18982, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-4742-578117", "node_context_10_4742_578117", "Original split at fuel 11 and node 578117",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 577686, 577851, 577984, 578116. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18982-579466", "node_context_11_18982_579466", "Original split at fuel 10 and node 579466",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 579386, 579420, 579447, 579465. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-4742-578117", "context_10_4742_578117", "Context at depth 10, code 4742, node 578117",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4742 and original node 578117, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_18968_577686, context_11_18969_577851, context_11_18970_577984, context_11_18971_578116.", DescribeRole.Theorem),
            Node("context-12-75932-579487", "context_12_75932_579487", "Context at depth 12, code 75932, node 579487",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75932 and original node 579487, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
