using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0078Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0078.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0078",
        H("Original frontier context coverage 0078"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03746", "selected_cut_03746", "Selected cut at depth 14, code 278705, node 118205",
                "At remaining fuel 7 and original index 118205, selection on the full partial prefix of depth 14 and code 278705 returns the complete row with depth 14, base-four code 278705, original node 118205, kind 2, reserved field 0, 1857 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03793", "selected_cut_03793", "Selected cut at depth 13, code 69781, node 120522",
                "At remaining fuel 8 and original index 120522, selection on the full partial prefix of depth 13 and code 69781 returns the complete row with depth 13, base-four code 69781, original node 120522, kind 2, reserved field 0, 1813 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-69676-118294", "unmarked_context_13_69676_118294", "Unmarked parent at depth 13, code 69676",
                "The frontier Boolean is false at remaining fuel 8, original node 118294, the whole prefixCache at depth 13 and code 69676, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4360-120430", "unmarked_context_11_4360_120430", "Unmarked parent at depth 11, code 4360",
                "The frontier Boolean is false at remaining fuel 10, original node 120430, the whole prefixCache at depth 11 and code 4360, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-69676-118294", "node_context_13_69676_118294", "Original split at fuel 8 and node 118294",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 118152, 118205, 118249, 118293. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4360-120430", "node_context_11_4360_120430", "Original split at fuel 10 and node 120430",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 118489, 119998, 120209, 120429. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-278705-118205", "context_14_278705_118205", "Context at depth 14, code 278705, node 118205",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 278705 and original node 118205, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-69781-120522", "context_13_69781_120522", "Context at depth 13, code 69781, node 120522",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 69781 and original node 120522, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
