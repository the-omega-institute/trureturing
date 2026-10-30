using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0176Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0176.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0176",
        H("Original frontier context coverage 0176"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08450", "selected_cut_08450", "Selected cut at depth 14, code 368720, node 236648",
                "At remaining fuel 7 and original index 236648, selection on the full partial prefix of depth 14 and code 368720 returns the complete row with depth 14, base-four code 368720, original node 236648, kind 2, reserved field 0, 1165 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08498", "selected_cut_08498", "Selected cut at depth 14, code 368807, node 238044",
                "At remaining fuel 7 and original index 238044, selection on the full partial prefix of depth 14 and code 368807 returns the complete row with depth 14, base-four code 368807, original node 238044, kind 2, reserved field 0, 1653 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-92180-236703", "unmarked_context_13_92180_236703", "Unmarked parent at depth 13, code 92180",
                "The frontier Boolean is false at remaining fuel 8, original node 236703, the whole prefixCache at depth 13 and code 92180, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-92201-238045", "unmarked_context_13_92201_238045", "Unmarked parent at depth 13, code 92201",
                "The frontier Boolean is false at remaining fuel 8, original node 238045, the whole prefixCache at depth 13 and code 92201, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-92180-236703", "node_context_13_92180_236703", "Original split at fuel 8 and node 236703",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 236648, 236666, 236681, 236702. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-92201-238045", "node_context_13_92201_238045", "Original split at fuel 8 and node 238045",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 237925, 237978, 238018, 238044. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-368720-236648", "context_14_368720_236648", "Context at depth 14, code 368720, node 236648",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 368720 and original node 236648, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-92201-238045", "context_13_92201_238045", "Context at depth 13, code 92201, node 238045",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92201 and original node 238045, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_368804_237925, context_14_368805_237978, context_14_368806_238018, context_14_368807_238044.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
