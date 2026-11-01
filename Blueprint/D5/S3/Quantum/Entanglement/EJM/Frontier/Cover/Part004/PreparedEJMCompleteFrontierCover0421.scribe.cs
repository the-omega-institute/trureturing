using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0421Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0421.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0421",
        H("Original frontier context coverage 0421"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20211", "selected_cut_20211", "Selected cut at depth 12, code 72624, node 517235",
                "At remaining fuel 9 and original index 517235, selection on the full partial prefix of depth 12 and code 72624 returns the complete row with depth 12, base-four code 72624, original node 517235, kind 2, reserved field 0, 1369 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20257", "selected_cut_20257", "Selected cut at depth 13, code 295000, node 518572",
                "At remaining fuel 8 and original index 518572, selection on the full partial prefix of depth 13 and code 295000 returns the complete row with depth 13, base-four code 295000, original node 518572, kind 2, reserved field 0, 1121 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18156-517278", "unmarked_context_11_18156_517278", "Unmarked parent at depth 11, code 18156",
                "The frontier Boolean is false at remaining fuel 10, original node 517278, the whole prefixCache at depth 11 and code 18156, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-73749-518546", "unmarked_context_12_73749_518546", "Unmarked parent at depth 12, code 73749",
                "The frontier Boolean is false at remaining fuel 9, original node 518546, the whole prefixCache at depth 12 and code 73749, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18156-517278", "node_context_11_18156_517278", "Original split at fuel 10 and node 517278",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 517235, 517250, 517264, 517277. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-73749-518546", "node_context_12_73749_518546", "Original split at fuel 9 and node 518546",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 518480, 518502, 518528, 518545. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-72624-517235", "context_12_72624_517235", "Context at depth 12, code 72624, node 517235",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72624 and original node 517235, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-295000-518572", "context_13_295000_518572", "Context at depth 13, code 295000, node 518572",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 295000 and original node 518572, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
