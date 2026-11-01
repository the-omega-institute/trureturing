using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0459Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0459.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0459",
        H("Original frontier context coverage 0459"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22035", "selected_cut_22035", "Selected cut at depth 12, code 75381, node 561922",
                "At remaining fuel 9 and original index 561922, selection on the full partial prefix of depth 12 and code 75381 returns the complete row with depth 12, base-four code 75381, original node 561922, kind 2, reserved field 0, 2713 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22082", "selected_cut_22082", "Selected cut at depth 12, code 75425, node 563011",
                "At remaining fuel 9 and original index 563011, selection on the full partial prefix of depth 12 and code 75425 returns the complete row with depth 12, base-four code 75425, original node 563011, kind 2, reserved field 0, 1465 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18845-562005", "unmarked_context_11_18845_562005", "Unmarked parent at depth 11, code 18845",
                "The frontier Boolean is false at remaining fuel 10, original node 562005, the whole prefixCache at depth 11 and code 18845, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4713-562984", "unmarked_context_10_4713_562984", "Unmarked parent at depth 10, code 4713",
                "The frontier Boolean is false at remaining fuel 11, original node 562984, the whole prefixCache at depth 10 and code 4713, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18845-562005", "node_context_11_18845_562005", "Original split at fuel 10 and node 562005",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 561889, 561922, 561958, 562004. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4713-562984", "node_context_10_4713_562984", "Original split at fuel 11 and node 562984",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 562725, 562833, 562902, 562983. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75381-561922", "context_12_75381_561922", "Context at depth 12, code 75381, node 561922",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75381 and original node 561922, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-75425-563011", "context_12_75425_563011", "Context at depth 12, code 75425, node 563011",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75425 and original node 563011, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
