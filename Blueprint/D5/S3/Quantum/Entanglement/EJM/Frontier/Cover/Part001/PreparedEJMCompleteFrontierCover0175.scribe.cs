using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0175Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0175.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0175",
        H("Original frontier context coverage 0175"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08403", "selected_cut_08403", "Selected cut at depth 12, code 22968, node 235248",
                "At remaining fuel 9 and original index 235248, selection on the full partial prefix of depth 12 and code 22968 returns the complete row with depth 12, base-four code 22968, original node 235248, kind 2, reserved field 0, 1145 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08449", "selected_cut_08449", "Selected cut at depth 13, code 92179, node 236624",
                "At remaining fuel 8 and original index 236624, selection on the full partial prefix of depth 13 and code 92179 returns the complete row with depth 13, base-four code 92179, original node 236624, kind 2, reserved field 0, 1461 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5742-235289", "unmarked_context_11_5742_235289", "Unmarked parent at depth 11, code 5742",
                "The frontier Boolean is false at remaining fuel 10, original node 235289, the whole prefixCache at depth 11 and code 5742, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23044-236625", "unmarked_context_12_23044_236625", "Unmarked parent at depth 12, code 23044",
                "The frontier Boolean is false at remaining fuel 9, original node 236625, the whole prefixCache at depth 12 and code 23044, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5742-235289", "node_context_11_5742_235289", "Original split at fuel 10 and node 235289",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 235248, 235260, 235274, 235288. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23044-236625", "node_context_12_23044_236625", "Original split at fuel 9 and node 236625",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 236384, 236523, 236579, 236624. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-22968-235248", "context_12_22968_235248", "Context at depth 12, code 22968, node 235248",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22968 and original node 235248, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-23044-236625", "context_12_23044_236625", "Context at depth 12, code 23044, node 236625",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23044 and original node 236625, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_92176_236384, context_13_92177_236523, context_13_92178_236579, context_13_92179_236624.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
