using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0584Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0584.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0584",
        H("Original frontier context coverage 0584"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28035", "selected_cut_28035", "Selected cut at depth 12, code 92004, node 707900",
                "At remaining fuel 9 and original index 707900, selection on the full partial prefix of depth 12 and code 92004 returns the complete row with depth 12, base-four code 92004, original node 707900, kind 2, reserved field 0, 2745 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28083", "selected_cut_28083", "Selected cut at depth 12, code 92043, node 709291",
                "At remaining fuel 9 and original index 709291, selection on the full partial prefix of depth 12 and code 92043 returns the complete row with depth 12, base-four code 92043, original node 709291, kind 2, reserved field 0, 2141 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23001-707987", "unmarked_context_11_23001_707987", "Unmarked parent at depth 11, code 23001",
                "The frontier Boolean is false at remaining fuel 10, original node 707987, the whole prefixCache at depth 11 and code 23001, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23009-709170", "unmarked_context_11_23009_709170", "Unmarked parent at depth 11, code 23009",
                "The frontier Boolean is false at remaining fuel 10, original node 709170, the whole prefixCache at depth 11 and code 23009, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23001-707987", "node_context_11_23001_707987", "Original split at fuel 10 and node 707987",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 707900, 642794, 707947, 707986. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23009-709170", "node_context_11_23009_709170", "Original split at fuel 10 and node 709170",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 709096, 709122, 709146, 709169. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-92004-707900", "context_12_92004_707900", "Context at depth 12, code 92004, node 707900",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 92004 and original node 707900, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-92043-709291", "context_12_92043_709291", "Context at depth 12, code 92043, node 709291",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 92043 and original node 709291, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
