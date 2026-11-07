using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0680Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0680.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0680",
        H("Original frontier context coverage 0680"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32644", "selected_cut_32644", "Selected cut at depth 13, code 438475, node 839851",
                "At remaining fuel 8 and original index 839851, selection on the full partial prefix of depth 13 and code 438475 returns the complete row with depth 13, base-four code 438475, original node 839851, kind 2, reserved field 0, 641 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32690", "selected_cut_32690", "Selected cut at depth 13, code 438551, node 840848",
                "At remaining fuel 8 and original index 840848, selection on the full partial prefix of depth 13 and code 438551 returns the complete row with depth 13, base-four code 438551, original node 840848, kind 2, reserved field 0, 693 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-109618-839852", "unmarked_context_12_109618_839852", "Unmarked parent at depth 12, code 109618",
                "The frontier Boolean is false at remaining fuel 9, original node 839852, the whole prefixCache at depth 12 and code 109618, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-109637-840849", "unmarked_context_12_109637_840849", "Unmarked parent at depth 12, code 109637",
                "The frontier Boolean is false at remaining fuel 9, original node 840849, the whole prefixCache at depth 12 and code 109637, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-109618-839852", "node_context_12_109618_839852", "Original split at fuel 9 and node 839852",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 839800, 839829, 839844, 839851. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-109637-840849", "node_context_12_109637_840849", "Original split at fuel 9 and node 840849",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 840810, 840836, 840848. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-438475-839851", "context_13_438475_839851", "Context at depth 13, code 438475, node 839851",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 438475 and original node 839851, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-109637-840849", "context_12_109637_840849", "Context at depth 12, code 109637, node 840849",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109637 and original node 840849, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_438548_3444, context_13_438549_840810, context_13_438550_840836, context_13_438551_840848.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
