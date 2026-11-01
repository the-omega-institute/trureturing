using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0994Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0994.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0994",
        H("Original frontier context coverage 0994"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47716", "selected_cut_47716", "Selected cut at depth 11, code 93520, node 1283168",
                "At remaining fuel 10 and original index 1283168, selection on the full partial prefix of depth 11 and code 93520 returns the complete row with depth 11, base-four code 93520, original node 1283168, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47762", "selected_cut_47762", "Selected cut at depth 12, code 374291, node 1337347",
                "At remaining fuel 9 and original index 1337347, selection on the full partial prefix of depth 12 and code 374291 returns the complete row with depth 12, base-four code 374291, original node 1337347, kind 2, reserved field 0, 3265 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23379-1335969", "unmarked_context_10_23379_1335969", "Unmarked parent at depth 10, code 23379",
                "The frontier Boolean is false at remaining fuel 11, original node 1335969, the whole prefixCache at depth 10 and code 23379, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93572-1337348", "unmarked_context_11_93572_1337348", "Unmarked parent at depth 11, code 93572",
                "The frontier Boolean is false at remaining fuel 10, original node 1337348, the whole prefixCache at depth 11 and code 93572, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23379-1335969", "node_context_10_23379_1335969", "Original split at fuel 11 and node 1335969",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1335698, 1335797, 1335909, 1335968. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93572-1337348", "node_context_11_93572_1337348", "Original split at fuel 10 and node 1337348",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1255011, 1337229, 1337280, 1337347. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23379-1335969", "context_10_23379_1335969", "Context at depth 10, code 23379, node 1335969",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23379 and original node 1335969, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_93516_1335698, context_11_93517_1335797, context_11_93518_1335909, context_11_93519_1335968.", DescribeRole.Theorem),
            Node("context-11-93572-1337348", "context_11_93572_1337348", "Context at depth 11, code 93572, node 1337348",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93572 and original node 1337348, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_374288_1255011, context_12_374289_1337229, context_12_374290_1337280, context_12_374291_1337347.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
