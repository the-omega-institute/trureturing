using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1041Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1041.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1041",
        H("Original frontier context coverage 1041"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49972", "selected_cut_49972", "Selected cut at depth 12, code 421147, node 1419288",
                "At remaining fuel 9 and original index 1419288, selection on the full partial prefix of depth 12 and code 421147 returns the complete row with depth 12, base-four code 421147, original node 1419288, kind 2, reserved field 0, 2337 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50019", "selected_cut_50019", "Selected cut at depth 12, code 421659, node 1421781",
                "At remaining fuel 9 and original index 1421781, selection on the full partial prefix of depth 12 and code 421659 returns the complete row with depth 12, base-four code 421659, original node 1421781, kind 2, reserved field 0, 2197 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-105286-1419289", "unmarked_context_11_105286_1419289", "Unmarked parent at depth 11, code 105286",
                "The frontier Boolean is false at remaining fuel 10, original node 1419289, the whole prefixCache at depth 11 and code 105286, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-105414-1421782", "unmarked_context_11_105414_1421782", "Unmarked parent at depth 11, code 105414",
                "The frontier Boolean is false at remaining fuel 10, original node 1421782, the whole prefixCache at depth 11 and code 105414, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-105286-1419289", "node_context_11_105286_1419289", "Original split at fuel 10 and node 1419289",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1415033, 1419214, 1415270, 1419288. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-105414-1421782", "node_context_11_105414_1421782", "Original split at fuel 10 and node 1421782",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1415033, 1421655, 1376651, 1421781. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-421147-1419288", "context_12_421147_1419288", "Context at depth 12, code 421147, node 1419288",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 421147 and original node 1419288, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-105414-1421782", "context_11_105414_1421782", "Context at depth 11, code 105414, node 1421782",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 105414 and original node 1421782, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_421656_1415033, context_12_421657_1421655, context_12_421658_1376651, context_12_421659_1421781.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
