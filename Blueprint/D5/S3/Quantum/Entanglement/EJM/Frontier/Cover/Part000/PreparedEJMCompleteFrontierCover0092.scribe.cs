using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0092Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0092.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0092",
        H("Original frontier context coverage 0092"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04418", "selected_cut_04418", "Selected cut at depth 13, code 73832, node 141317",
                "At remaining fuel 8 and original index 141317, selection on the full partial prefix of depth 13 and code 73832 returns the complete row with depth 13, base-four code 73832, original node 141317, kind 2, reserved field 0, 1845 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04465", "selected_cut_04465", "Selected cut at depth 13, code 73891, node 143205",
                "At remaining fuel 8 and original index 143205, selection on the full partial prefix of depth 13 and code 73891 returns the complete row with depth 13, base-four code 73891, original node 143205, kind 2, reserved field 0, 293 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18458-141413", "unmarked_context_12_18458_141413", "Unmarked parent at depth 12, code 18458",
                "The frontier Boolean is false at remaining fuel 9, original node 141413, the whole prefixCache at depth 12 and code 18458, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-18472-143206", "unmarked_context_12_18472_143206", "Unmarked parent at depth 12, code 18472",
                "The frontier Boolean is false at remaining fuel 9, original node 143206, the whole prefixCache at depth 12 and code 18472, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18458-141413", "node_context_12_18458_141413", "Original split at fuel 9 and node 141413",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 141317, 141382, 141404, 141412. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-18472-143206", "node_context_12_18472_143206", "Original split at fuel 9 and node 143206",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 143009, 143174, 143193, 143205. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-73832-141317", "context_13_73832_141317", "Context at depth 13, code 73832, node 141317",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 73832 and original node 141317, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-18472-143206", "context_12_18472_143206", "Context at depth 12, code 18472, node 143206",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18472 and original node 143206, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_73888_143009, context_13_73889_143174, context_13_73890_143193, context_13_73891_143205.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
