using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0803Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0803.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0803",
        H("Original frontier context coverage 0803"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38548", "selected_cut_38548", "Selected cut at depth 12, code 301624, node 1040189",
                "At remaining fuel 9 and original index 1040189, selection on the full partial prefix of depth 12 and code 301624 returns the complete row with depth 12, base-four code 301624, original node 1040189, kind 2, reserved field 0, 2749 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38595", "selected_cut_38595", "Selected cut at depth 12, code 301689, node 1041696",
                "At remaining fuel 9 and original index 1041696, selection on the full partial prefix of depth 12 and code 301689 returns the complete row with depth 12, base-four code 301689, original node 1041696, kind 2, reserved field 0, 1789 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75405-1040143", "unmarked_context_11_75405_1040143", "Unmarked parent at depth 11, code 75405",
                "The frontier Boolean is false at remaining fuel 10, original node 1040143, the whole prefixCache at depth 11 and code 75405, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75421-1041632", "unmarked_context_11_75421_1041632", "Unmarked parent at depth 11, code 75421",
                "The frontier Boolean is false at remaining fuel 10, original node 1041632, the whole prefixCache at depth 11 and code 75421, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75405-1040143", "node_context_11_75405_1040143", "Original split at fuel 10 and node 1040143",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1039954, 1040026, 1040077, 1040142. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75421-1041632", "node_context_11_75421_1041632", "Original split at fuel 10 and node 1041632",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1041580, 691709, 1041600, 1041631. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-75405-1040143", "context_11_75405_1040143", "Context at depth 11, code 75405, node 1040143",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75405 and original node 1040143, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_301620_1039954, context_12_301621_1040026, context_12_301622_1040077, context_12_301623_1040142.", DescribeRole.Theorem),
            Node("context-12-301689-1041696", "context_12_301689_1041696", "Context at depth 12, code 301689, node 1041696",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301689 and original node 1041696, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
