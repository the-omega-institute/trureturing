using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0798Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0798.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0798",
        H("Original frontier context coverage 0798"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38307", "selected_cut_38307", "Selected cut at depth 12, code 301194, node 984676",
                "At remaining fuel 9 and original index 984676, selection on the full partial prefix of depth 12 and code 301194 returns the complete row with depth 12, base-four code 301194, original node 984676, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38354", "selected_cut_38354", "Selected cut at depth 12, code 301331, node 1033318",
                "At remaining fuel 9 and original index 1033318, selection on the full partial prefix of depth 12 and code 301331 returns the complete row with depth 12, base-four code 301331, original node 1033318, kind 2, reserved field 0, 2377 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75298-1031505", "unmarked_context_11_75298_1031505", "Unmarked parent at depth 11, code 75298",
                "The frontier Boolean is false at remaining fuel 10, original node 1031505, the whole prefixCache at depth 11 and code 75298, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18832-1033147", "unmarked_context_10_18832_1033147", "Unmarked parent at depth 10, code 18832",
                "The frontier Boolean is false at remaining fuel 11, original node 1033147, the whole prefixCache at depth 10 and code 18832, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75298-1031505", "node_context_11_75298_1031505", "Original split at fuel 10 and node 1031505",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1031454, 1031479, 984676, 1031504. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18832-1033147", "node_context_10_18832_1033147", "Original split at fuel 11 and node 1033147",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1032441, 1032687, 1032901, 1033146. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-301194-984676", "context_12_301194_984676", "Context at depth 12, code 301194, node 984676",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301194 and original node 984676, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-301331-1033318", "context_12_301331_1033318", "Context at depth 12, code 301331, node 1033318",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301331 and original node 1033318, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
