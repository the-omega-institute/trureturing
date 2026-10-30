using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0589Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0589.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0589",
        H("Original frontier context coverage 0589"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28276", "selected_cut_28276", "Selected cut at depth 10, code 5764, node 145424",
                "At remaining fuel 11 and original index 145424, selection on the full partial prefix of depth 10 and code 5764 returns the complete row with depth 10, base-four code 5764, original node 145424, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28322", "selected_cut_28322", "Selected cut at depth 11, code 23078, node 715756",
                "At remaining fuel 10 and original index 715756, selection on the full partial prefix of depth 11 and code 23078 returns the complete row with depth 11, base-four code 23078, original node 715756, kind 2, reserved field 0, 1461 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23055-714249", "unmarked_context_11_23055_714249", "Unmarked parent at depth 11, code 23055",
                "The frontier Boolean is false at remaining fuel 10, original node 714249, the whole prefixCache at depth 11 and code 23055, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23076-715669", "unmarked_context_11_23076_715669", "Unmarked parent at depth 11, code 23076",
                "The frontier Boolean is false at remaining fuel 10, original node 715669, the whole prefixCache at depth 11 and code 23076, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23055-714249", "node_context_11_23055_714249", "Original split at fuel 10 and node 714249",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 714076, 714133, 714188, 714248. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23076-715669", "node_context_11_23076_715669", "Original split at fuel 10 and node 715669",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 715604, 715628, 715651, 715668. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-23055-714249", "context_11_23055_714249", "Context at depth 11, code 23055, node 714249",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 23055 and original node 714249, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_92220_714076, context_12_92221_714133, context_12_92222_714188, context_12_92223_714248.", DescribeRole.Theorem),
            Node("context-11-23078-715756", "context_11_23078_715756", "Context at depth 11, code 23078, node 715756",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 23078 and original node 715756, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
