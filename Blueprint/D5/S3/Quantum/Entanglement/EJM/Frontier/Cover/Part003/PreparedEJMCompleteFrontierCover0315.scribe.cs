using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0315Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0315.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0315",
        H("Original frontier context coverage 0315"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15123", "selected_cut_15123", "Selected cut at depth 12, code 27648, node 34034",
                "At remaining fuel 9 and original index 34034, selection on the full partial prefix of depth 12 and code 27648 returns the complete row with depth 12, base-four code 27648, original node 34034, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15170", "selected_cut_15170", "Selected cut at depth 13, code 110648, node 390617",
                "At remaining fuel 8 and original index 390617, selection on the full partial prefix of depth 13 and code 110648 returns the complete row with depth 13, base-four code 110648, original node 390617, kind 2, reserved field 0, 2933 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-8-107-388827", "unmarked_context_8_107_388827", "Unmarked parent at depth 8, code 107",
                "The frontier Boolean is false at remaining fuel 13, original node 388827, the whole prefixCache at depth 8 and code 107, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27661-390565", "unmarked_context_12_27661_390565", "Unmarked parent at depth 12, code 27661",
                "The frontier Boolean is false at remaining fuel 9, original node 390565, the whole prefixCache at depth 12 and code 27661, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-8-107-388827", "node_context_8_107_388827", "Original split at fuel 13 and node 388827",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 383026, 387264, 388492, 388826. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27661-390565", "node_context_12_27661_390565", "Original split at fuel 9 and node 390565",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 390479, 390532, 390557, 390564. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-8-107-388827", "context_8_107_388827", "Context at depth 8, code 107, node 388827",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 107 and original node 388827, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_9_428_383026, context_9_429_387264, context_9_430_388492, context_9_431_388826.", DescribeRole.Theorem),
            Node("context-13-110648-390617", "context_13_110648_390617", "Context at depth 13, code 110648, node 390617",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 110648 and original node 390617, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
