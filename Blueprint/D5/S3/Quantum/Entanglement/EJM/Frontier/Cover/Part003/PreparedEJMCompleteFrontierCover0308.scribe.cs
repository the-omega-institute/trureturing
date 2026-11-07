using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0308Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0308.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0308",
        H("Original frontier context coverage 0308"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14788", "selected_cut_14788", "Selected cut at depth 13, code 109723, node 381086",
                "At remaining fuel 8 and original index 381086, selection on the full partial prefix of depth 13 and code 109723 returns the complete row with depth 13, base-four code 109723, original node 381086, kind 2, reserved field 0, 845 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14835", "selected_cut_14835", "Selected cut at depth 13, code 109773, node 382246",
                "At remaining fuel 8 and original index 382246, selection on the full partial prefix of depth 13 and code 109773 returns the complete row with depth 13, base-four code 109773, original node 382246, kind 2, reserved field 0, 2549 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27430-381087", "unmarked_context_12_27430_381087", "Unmarked parent at depth 12, code 27430",
                "The frontier Boolean is false at remaining fuel 9, original node 381087, the whole prefixCache at depth 12 and code 27430, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27442-382214", "unmarked_context_12_27442_382214", "Unmarked parent at depth 12, code 27442",
                "The frontier Boolean is false at remaining fuel 9, original node 382214, the whole prefixCache at depth 12 and code 27442, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27430-381087", "node_context_12_27430_381087", "Original split at fuel 9 and node 381087",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 381041, 381066, 381082, 381086. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27442-382214", "node_context_12_27442_382214", "Original split at fuel 9 and node 382214",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 382160, 382186, 382209, 382213. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-109723-381086", "context_13_109723_381086", "Context at depth 13, code 109723, node 381086",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109723 and original node 381086, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-109773-382246", "context_13_109773_382246", "Context at depth 13, code 109773, node 382246",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109773 and original node 382246, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
