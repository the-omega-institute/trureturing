using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0705Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0705.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0705",
        H("Original frontier context coverage 0705"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33843", "selected_cut_33843", "Selected cut at depth 13, code 450642, node 871769",
                "At remaining fuel 8 and original index 871769, selection on the full partial prefix of depth 13 and code 450642 returns the complete row with depth 13, base-four code 450642, original node 871769, kind 2, reserved field 0, 917 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33890", "selected_cut_33890", "Selected cut at depth 13, code 450692, node 872967",
                "At remaining fuel 8 and original index 872967, selection on the full partial prefix of depth 13 and code 450692 returns the complete row with depth 13, base-four code 450692, original node 872967, kind 2, reserved field 0, 1069 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-112660-871782", "unmarked_context_12_112660_871782", "Unmarked parent at depth 12, code 112660",
                "The frontier Boolean is false at remaining fuel 9, original node 871782, the whole prefixCache at depth 12 and code 112660, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-7041-872927", "unmarked_context_10_7041_872927", "Unmarked parent at depth 10, code 7041",
                "The frontier Boolean is false at remaining fuel 11, original node 872927, the whole prefixCache at depth 10 and code 7041, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-112660-871782", "node_context_12_112660_871782", "Original split at fuel 9 and node 871782",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 871720, 871746, 871769, 871781. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-7041-872927", "node_context_10_7041_872927", "Original split at fuel 11 and node 872927",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 871699, 872079, 872450, 872926. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-450642-871769", "context_13_450642_871769", "Context at depth 13, code 450642, node 871769",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 450642 and original node 871769, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-450692-872967", "context_13_450692_872967", "Context at depth 13, code 450692, node 872967",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 450692 and original node 872967, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
