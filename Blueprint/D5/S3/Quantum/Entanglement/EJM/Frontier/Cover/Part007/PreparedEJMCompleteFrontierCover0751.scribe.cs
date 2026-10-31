using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0751Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0751.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0751",
        H("Original frontier context coverage 0751"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36050", "selected_cut_36050", "Selected cut at depth 12, code 288017, node 950743",
                "At remaining fuel 9 and original index 950743, selection on the full partial prefix of depth 12 and code 288017 returns the complete row with depth 12, base-four code 288017, original node 950743, kind 2, reserved field 0, 1501 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36097", "selected_cut_36097", "Selected cut at depth 12, code 288079, node 952779",
                "At remaining fuel 9 and original index 952779, selection on the full partial prefix of depth 12 and code 288079 returns the complete row with depth 12, base-four code 288079, original node 952779, kind 2, reserved field 0, 1965 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-72004-950842", "unmarked_context_11_72004_950842", "Unmarked parent at depth 11, code 72004",
                "The frontier Boolean is false at remaining fuel 10, original node 950842, the whole prefixCache at depth 11 and code 72004, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18004-952781", "unmarked_context_10_18004_952781", "Unmarked parent at depth 10, code 18004",
                "The frontier Boolean is false at remaining fuel 11, original node 952781, the whole prefixCache at depth 10 and code 18004, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-72004-950842", "node_context_11_72004_950842", "Original split at fuel 10 and node 950842",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 950743, 950792, 950841. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18004-952781", "node_context_10_18004_952781", "Original split at fuel 11 and node 952781",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 952268, 952414, 952632, 952780. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-288017-950743", "context_12_288017_950743", "Context at depth 12, code 288017, node 950743",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 288017 and original node 950743, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-18004-952781", "context_10_18004_952781", "Context at depth 10, code 18004, node 952781",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18004 and original node 952781, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_72016_952268, context_11_72017_952414, context_11_72018_952632, context_11_72019_952780.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
