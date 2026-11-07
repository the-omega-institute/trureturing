using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0296Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0296.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0296",
        H("Original frontier context coverage 0296"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14211", "selected_cut_14211", "Selected cut at depth 13, code 108600, node 368694",
                "At remaining fuel 8 and original index 368694, selection on the full partial prefix of depth 13 and code 108600 returns the complete row with depth 13, base-four code 108600, original node 368694, kind 2, reserved field 0, 2857 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14258", "selected_cut_14258", "Selected cut at depth 13, code 108647, node 369749",
                "At remaining fuel 8 and original index 369749, selection on the full partial prefix of depth 13 and code 108647 returns the complete row with depth 13, base-four code 108647, original node 369749, kind 2, reserved field 0, 837 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27150-368800", "unmarked_context_12_27150_368800", "Unmarked parent at depth 12, code 27150",
                "The frontier Boolean is false at remaining fuel 9, original node 368800, the whole prefixCache at depth 12 and code 27150, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27161-369750", "unmarked_context_12_27161_369750", "Unmarked parent at depth 12, code 27161",
                "The frontier Boolean is false at remaining fuel 9, original node 369750, the whole prefixCache at depth 12 and code 27161, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27150-368800", "node_context_12_27150_368800", "Original split at fuel 9 and node 368800",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 368694, 368758, 368790, 368799. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27161-369750", "node_context_12_27161_369750", "Original split at fuel 9 and node 369750",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 369704, 369727, 369741, 369749. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-108600-368694", "context_13_108600_368694", "Context at depth 13, code 108600, node 368694",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 108600 and original node 368694, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27161-369750", "context_12_27161_369750", "Context at depth 12, code 27161, node 369750",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27161 and original node 369750, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_108644_369704, context_13_108645_369727, context_13_108646_369741, context_13_108647_369749.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
