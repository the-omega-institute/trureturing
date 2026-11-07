using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1079Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1079.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1079",
        H("Original frontier context coverage 1079"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51795", "selected_cut_51795", "Selected cut at depth 11, code 284943, node 1470044",
                "At remaining fuel 10 and original index 1470044, selection on the full partial prefix of depth 11 and code 284943 returns the complete row with depth 11, base-four code 284943, original node 1470044, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51842", "selected_cut_51842", "Selected cut at depth 9, code 17819, node 1499848",
                "At remaining fuel 12 and original index 1499848, selection on the full partial prefix of depth 9 and code 17819 returns the complete row with depth 9, base-four code 17819, original node 1499848, kind 2, reserved field 0, 497 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-71235-1497593", "unmarked_context_10_71235_1497593", "Unmarked parent at depth 10, code 71235",
                "The frontier Boolean is false at remaining fuel 11, original node 1497593, the whole prefixCache at depth 10 and code 71235, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-17817-1499697", "unmarked_context_9_17817_1499697", "Unmarked parent at depth 9, code 17817",
                "The frontier Boolean is false at remaining fuel 12, original node 1499697, the whole prefixCache at depth 9 and code 17817, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-71235-1497593", "node_context_10_71235_1497593", "Original split at fuel 11 and node 1497593",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1497515, 1497552, 1497592, 1470044. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-17817-1499697", "node_context_9_17817_1499697", "Original split at fuel 12 and node 1499697",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1499521, 1468874, 1499651, 1499696. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-284943-1470044", "context_11_284943_1470044", "Context at depth 11, code 284943, node 1470044",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 284943 and original node 1470044, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-17819-1499848", "context_9_17819_1499848", "Context at depth 9, code 17819, node 1499848",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 17819 and original node 1499848, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
