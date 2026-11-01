using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0744Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0744.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0744",
        H("Original frontier context coverage 0744"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35715", "selected_cut_35715", "Selected cut at depth 13, code 1148979, node 940107",
                "At remaining fuel 8 and original index 940107, selection on the full partial prefix of depth 13 and code 1148979 returns the complete row with depth 13, base-four code 1148979, original node 940107, kind 2, reserved field 0, 689 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35762", "selected_cut_35762", "Selected cut at depth 12, code 287285, node 942182",
                "At remaining fuel 9 and original index 942182, selection on the full partial prefix of depth 12 and code 287285 returns the complete row with depth 12, base-four code 287285, original node 942182, kind 2, reserved field 0, 2565 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-287244-940108", "unmarked_context_12_287244_940108", "Unmarked parent at depth 12, code 287244",
                "The frontier Boolean is false at remaining fuel 9, original node 940108, the whole prefixCache at depth 12 and code 287244, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71820-942096", "unmarked_context_11_71820_942096", "Unmarked parent at depth 11, code 71820",
                "The frontier Boolean is false at remaining fuel 10, original node 942096, the whole prefixCache at depth 11 and code 71820, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-287244-940108", "node_context_12_287244_940108", "Original split at fuel 9 and node 940108",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 940059, 940080, 940102, 940107. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71820-942096", "node_context_11_71820_942096", "Original split at fuel 10 and node 942096",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 941981, 942013, 942045, 942095. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1148979-940107", "context_13_1148979_940107", "Context at depth 13, code 1148979, node 940107",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1148979 and original node 940107, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-287285-942182", "context_12_287285_942182", "Context at depth 12, code 287285, node 942182",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287285 and original node 942182, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
