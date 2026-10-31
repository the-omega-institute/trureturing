using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0864Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0864.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0864",
        H("Original frontier context coverage 0864"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41475", "selected_cut_41475", "Selected cut at depth 12, code 335976, node 1134046",
                "At remaining fuel 9 and original index 1134046, selection on the full partial prefix of depth 12 and code 335976 returns the complete row with depth 12, base-four code 335976, original node 1134046, kind 2, reserved field 0, 1537 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41521", "selected_cut_41521", "Selected cut at depth 11, code 84019, node 1135154",
                "At remaining fuel 10 and original index 1135154, selection on the full partial prefix of depth 11 and code 84019 returns the complete row with depth 11, base-four code 84019, original node 1135154, kind 2, reserved field 0, 1141 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83993-1134023", "unmarked_context_11_83993_1134023", "Unmarked parent at depth 11, code 83993",
                "The frontier Boolean is false at remaining fuel 10, original node 1134023, the whole prefixCache at depth 11 and code 83993, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21004-1135155", "unmarked_context_10_21004_1135155", "Unmarked parent at depth 10, code 21004",
                "The frontier Boolean is false at remaining fuel 11, original node 1135155, the whole prefixCache at depth 10 and code 21004, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83993-1134023", "node_context_11_83993_1134023", "Original split at fuel 10 and node 1134023",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1133973, 642794, 1134000, 1134022. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21004-1135155", "node_context_10_21004_1135155", "Original split at fuel 11 and node 1135155",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 1135119, 1135136, 1135154. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-83993-1134023", "context_11_83993_1134023", "Context at depth 11, code 83993, node 1134023",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 83993 and original node 1134023, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_335972_1133973, context_12_335973_642794, context_12_335974_1134000, context_12_335975_1134022.", DescribeRole.Theorem),
            Node("context-10-21004-1135155", "context_10_21004_1135155", "Context at depth 10, code 21004, node 1135155",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21004 and original node 1135155, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_84016_907917, context_11_84017_1135119, context_11_84018_1135136, context_11_84019_1135154.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
