using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0476Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0476.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0476",
        H("Original frontier context coverage 0476"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22850", "selected_cut_22850", "Selected cut at depth 12, code 76040, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 76040 returns the complete row with depth 12, base-four code 76040, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22898", "selected_cut_22898", "Selected cut at depth 13, code 304235, node 581262",
                "At remaining fuel 8 and original index 581262, selection on the full partial prefix of depth 13 and code 304235 returns the complete row with depth 13, base-four code 304235, original node 581262, kind 2, reserved field 0, 909 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76041-580545", "unmarked_context_12_76041_580545", "Unmarked parent at depth 12, code 76041",
                "The frontier Boolean is false at remaining fuel 9, original node 580545, the whole prefixCache at depth 12 and code 76041, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76058-581263", "unmarked_context_12_76058_581263", "Unmarked parent at depth 12, code 76058",
                "The frontier Boolean is false at remaining fuel 9, original node 581263, the whole prefixCache at depth 12 and code 76058, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76041-580545", "node_context_12_76041_580545", "Original split at fuel 9 and node 580545",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 580489, 580517, 580537, 580544. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76058-581263", "node_context_12_76058_581263", "Original split at fuel 9 and node 581263",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 581216, 581238, 581256, 581262. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76040-448748", "context_12_76040_448748", "Context at depth 12, code 76040, node 448748",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76040 and original node 448748, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-76058-581263", "context_12_76058_581263", "Context at depth 12, code 76058, node 581263",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76058 and original node 581263, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_304232_581216, context_13_304233_581238, context_13_304234_581256, context_13_304235_581262.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
