using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0416Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0416.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0416",
        H("Original frontier context coverage 0416"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19972", "selected_cut_19972", "Selected cut at depth 13, code 289978, node 511357",
                "At remaining fuel 8 and original index 511357, selection on the full partial prefix of depth 13 and code 289978 returns the complete row with depth 13, base-four code 289978, original node 511357, kind 2, reserved field 0, 1853 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20019", "selected_cut_20019", "Selected cut at depth 13, code 290028, node 512378",
                "At remaining fuel 8 and original index 512378, selection on the full partial prefix of depth 13 and code 290028 returns the complete row with depth 13, base-four code 290028, original node 512378, kind 2, reserved field 0, 121 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72494-511364", "unmarked_context_12_72494_511364", "Unmarked parent at depth 12, code 72494",
                "The frontier Boolean is false at remaining fuel 9, original node 511364, the whole prefixCache at depth 12 and code 72494, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72506-512375", "unmarked_context_12_72506_512375", "Unmarked parent at depth 12, code 72506",
                "The frontier Boolean is false at remaining fuel 9, original node 512375, the whole prefixCache at depth 12 and code 72506, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72494-511364", "node_context_12_72494_511364", "Original split at fuel 9 and node 511364",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 511294, 511333, 511357, 511363. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72506-512375", "node_context_12_72506_512375", "Original split at fuel 9 and node 512375",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 512316, 512343, 512366, 512374. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-289978-511357", "context_13_289978_511357", "Context at depth 13, code 289978, node 511357",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 289978 and original node 511357, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-290028-512378", "context_13_290028_512378", "Context at depth 13, code 290028, node 512378",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 290028 and original node 512378, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
