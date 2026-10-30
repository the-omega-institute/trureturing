using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0613Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0613.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0613",
        H("Original frontier context coverage 0613"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29427", "selected_cut_29427", "Selected cut at depth 13, code 374019, node 742473",
                "At remaining fuel 8 and original index 742473, selection on the full partial prefix of depth 13 and code 374019 returns the complete row with depth 13, base-four code 374019, original node 742473, kind 2, reserved field 0, 777 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29475", "selected_cut_29475", "Selected cut at depth 12, code 93546, node 743897",
                "At remaining fuel 9 and original index 743897, selection on the full partial prefix of depth 12 and code 93546 returns the complete row with depth 12, base-four code 93546, original node 743897, kind 2, reserved field 0, 3045 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93504-742474", "unmarked_context_12_93504_742474", "Unmarked parent at depth 12, code 93504",
                "The frontier Boolean is false at remaining fuel 9, original node 742474, the whole prefixCache at depth 12 and code 93504, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23385-743807", "unmarked_context_11_23385_743807", "Unmarked parent at depth 11, code 23385",
                "The frontier Boolean is false at remaining fuel 10, original node 743807, the whole prefixCache at depth 11 and code 23385, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93504-742474", "node_context_12_93504_742474", "Original split at fuel 9 and node 742474",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 742441, 742464, 742473. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23385-743807", "node_context_11_23385_743807", "Original split at fuel 10 and node 743807",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 743719, 642794, 743760, 743806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-374019-742473", "context_13_374019_742473", "Context at depth 13, code 374019, node 742473",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 374019 and original node 742473, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93546-743897", "context_12_93546_743897", "Context at depth 12, code 93546, node 743897",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93546 and original node 743897, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
