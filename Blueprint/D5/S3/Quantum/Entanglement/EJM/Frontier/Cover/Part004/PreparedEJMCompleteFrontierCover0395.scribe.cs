using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0395Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0395.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0395",
        H("Original frontier context coverage 0395"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18963", "selected_cut_18963", "Selected cut at depth 13, code 287910, node 486130",
                "At remaining fuel 8 and original index 486130, selection on the full partial prefix of depth 13 and code 287910 returns the complete row with depth 13, base-four code 287910, original node 486130, kind 2, reserved field 0, 2189 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19010", "selected_cut_19010", "Selected cut at depth 13, code 287960, node 487426",
                "At remaining fuel 8 and original index 487426, selection on the full partial prefix of depth 13 and code 287960 returns the complete row with depth 13, base-four code 287960, original node 487426, kind 2, reserved field 0, 801 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71977-486156", "unmarked_context_12_71977_486156", "Unmarked parent at depth 12, code 71977",
                "The frontier Boolean is false at remaining fuel 9, original node 486156, the whole prefixCache at depth 12 and code 71977, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71989-487415", "unmarked_context_12_71989_487415", "Unmarked parent at depth 12, code 71989",
                "The frontier Boolean is false at remaining fuel 9, original node 487415, the whole prefixCache at depth 12 and code 71989, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71977-486156", "node_context_12_71977_486156", "Original split at fuel 9 and node 486156",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 486072, 486107, 486130, 486155. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71989-487415", "node_context_12_71989_487415", "Original split at fuel 9 and node 487415",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 487249, 487327, 487381, 487414. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-287910-486130", "context_13_287910_486130", "Context at depth 13, code 287910, node 486130",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287910 and original node 486130, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-287960-487426", "context_13_287960_487426", "Context at depth 13, code 287960, node 487426",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287960 and original node 487426, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
