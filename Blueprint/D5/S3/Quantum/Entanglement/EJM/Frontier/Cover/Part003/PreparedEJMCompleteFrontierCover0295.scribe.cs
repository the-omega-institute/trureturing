using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0295Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0295.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0295",
        H("Original frontier context coverage 0295"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14163", "selected_cut_14163", "Selected cut at depth 14, code 434259, node 367147",
                "At remaining fuel 7 and original index 367147, selection on the full partial prefix of depth 14 and code 434259 returns the complete row with depth 14, base-four code 434259, original node 367147, kind 2, reserved field 0, 1033 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14210", "selected_cut_14210", "Selected cut at depth 13, code 108599, node 368646",
                "At remaining fuel 8 and original index 368646, selection on the full partial prefix of depth 13 and code 108599 returns the complete row with depth 13, base-four code 108599, original node 368646, kind 2, reserved field 0, 1093 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-108564-367148", "unmarked_context_13_108564_367148", "Unmarked parent at depth 13, code 108564",
                "The frontier Boolean is false at remaining fuel 8, original node 367148, the whole prefixCache at depth 13 and code 108564, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27149-368647", "unmarked_context_12_27149_368647", "Unmarked parent at depth 12, code 27149",
                "The frontier Boolean is false at remaining fuel 9, original node 368647, the whole prefixCache at depth 12 and code 27149, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-108564-367148", "node_context_13_108564_367148", "Original split at fuel 8 and node 367148",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 367110, 367125, 367136, 367147. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27149-368647", "node_context_12_27149_368647", "Original split at fuel 9 and node 368647",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 368549, 368614, 368638, 368646. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-434259-367147", "context_14_434259_367147", "Context at depth 14, code 434259, node 367147",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 434259 and original node 367147, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27149-368647", "context_12_27149_368647", "Context at depth 12, code 27149, node 368647",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27149 and original node 368647, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_108596_368549, context_13_108597_368614, context_13_108598_368638, context_13_108599_368646.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
