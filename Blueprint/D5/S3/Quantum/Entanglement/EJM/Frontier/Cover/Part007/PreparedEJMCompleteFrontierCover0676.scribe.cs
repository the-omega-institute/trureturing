using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0676Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0676.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0676",
        H("Original frontier context coverage 0676"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32451", "selected_cut_32451", "Selected cut at depth 11, code 27093, node 451541",
                "At remaining fuel 10 and original index 451541, selection on the full partial prefix of depth 11 and code 27093 returns the complete row with depth 11, base-four code 27093, original node 451541, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32498", "selected_cut_32498", "Selected cut at depth 12, code 109574, node 763842",
                "At remaining fuel 9 and original index 763842, selection on the full partial prefix of depth 12 and code 109574 returns the complete row with depth 12, base-four code 109574, original node 763842, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-27094-834731", "unmarked_context_11_27094_834731", "Unmarked parent at depth 11, code 27094",
                "The frontier Boolean is false at remaining fuel 10, original node 834731, the whole prefixCache at depth 11 and code 27094, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-7-105-836035", "unmarked_context_7_105_836035", "Unmarked parent at depth 7, code 105",
                "The frontier Boolean is false at remaining fuel 14, original node 836035, the whole prefixCache at depth 7 and code 105, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-27094-834731", "node_context_11_27094_834731", "Original split at fuel 10 and node 834731",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 834592, 834636, 834676, 834730. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-7-105-836035", "node_context_7_105_836035", "Original split at fuel 14 and node 836035",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 820921, 829801, 158379, 836034. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-27093-451541", "context_11_27093_451541", "Context at depth 11, code 27093, node 451541",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27093 and original node 451541, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-109574-763842", "context_12_109574_763842", "Context at depth 12, code 109574, node 763842",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109574 and original node 763842, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
