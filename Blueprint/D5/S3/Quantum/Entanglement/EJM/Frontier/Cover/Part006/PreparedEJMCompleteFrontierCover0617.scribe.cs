using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0617Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0617.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0617",
        H("Original frontier context coverage 0617"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29619", "selected_cut_29619", "Selected cut at depth 13, code 374868, node 748003",
                "At remaining fuel 8 and original index 748003, selection on the full partial prefix of depth 13 and code 374868 returns the complete row with depth 13, base-four code 374868, original node 748003, kind 2, reserved field 0, 2225 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29666", "selected_cut_29666", "Selected cut at depth 13, code 374915, node 749050",
                "At remaining fuel 8 and original index 749050, selection on the full partial prefix of depth 13 and code 374915 returns the complete row with depth 13, base-four code 374915, original node 749050, kind 2, reserved field 0, 645 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93717-748059", "unmarked_context_12_93717_748059", "Unmarked parent at depth 12, code 93717",
                "The frontier Boolean is false at remaining fuel 9, original node 748059, the whole prefixCache at depth 12 and code 93717, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93728-749051", "unmarked_context_12_93728_749051", "Unmarked parent at depth 12, code 93728",
                "The frontier Boolean is false at remaining fuel 9, original node 749051, the whole prefixCache at depth 12 and code 93728, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93717-748059", "node_context_12_93717_748059", "Original split at fuel 9 and node 748059",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 748003, 748026, 748049, 748058. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93728-749051", "node_context_12_93728_749051", "Original split at fuel 9 and node 749051",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 749001, 749024, 749043, 749050. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-374868-748003", "context_13_374868_748003", "Context at depth 13, code 374868, node 748003",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 374868 and original node 748003, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93728-749051", "context_12_93728_749051", "Context at depth 12, code 93728, node 749051",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93728 and original node 749051, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_374912_749001, context_13_374913_749024, context_13_374914_749043, context_13_374915_749050.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
