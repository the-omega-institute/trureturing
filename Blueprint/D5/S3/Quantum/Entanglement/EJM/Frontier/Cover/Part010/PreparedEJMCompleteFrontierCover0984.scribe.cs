using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0984Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0984.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0984",
        H("Original frontier context coverage 0984"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47235", "selected_cut_47235", "Selected cut at depth 12, code 372765, node 1321577",
                "At remaining fuel 9 and original index 1321577, selection on the full partial prefix of depth 12 and code 372765 returns the complete row with depth 12, base-four code 372765, original node 1321577, kind 2, reserved field 0, 2429 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47282", "selected_cut_47282", "Selected cut at depth 11, code 93212, node 1322915",
                "At remaining fuel 10 and original index 1322915, selection on the full partial prefix of depth 11 and code 93212 returns the complete row with depth 11, base-four code 93212, original node 1322915, kind 2, reserved field 0, 3237 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93191-1321656", "unmarked_context_11_93191_1321656", "Unmarked parent at depth 11, code 93191",
                "The frontier Boolean is false at remaining fuel 10, original node 1321656, the whole prefixCache at depth 11 and code 93191, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23302-1322866", "unmarked_context_10_23302_1322866", "Unmarked parent at depth 10, code 23302",
                "The frontier Boolean is false at remaining fuel 11, original node 1322866, the whole prefixCache at depth 10 and code 23302, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93191-1321656", "node_context_11_93191_1321656", "Original split at fuel 10 and node 1321656",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1321536, 1321577, 1321617, 1321655. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23302-1322866", "node_context_10_23302_1322866", "Original split at fuel 11 and node 1322866",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1322642, 1322741, 1322767, 1322865. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-372765-1321577", "context_12_372765_1321577", "Context at depth 12, code 372765, node 1321577",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 372765 and original node 1321577, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-93212-1322915", "context_11_93212_1322915", "Context at depth 11, code 93212, node 1322915",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93212 and original node 1322915, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
