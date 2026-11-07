using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0098Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0098.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0098",
        H("Original frontier context coverage 0098"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04706", "selected_cut_04706", "Selected cut at depth 13, code 74897, node 151241",
                "At remaining fuel 8 and original index 151241, selection on the full partial prefix of depth 13 and code 74897 returns the complete row with depth 13, base-four code 74897, original node 151241, kind 2, reserved field 0, 2385 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04755", "selected_cut_04755", "Selected cut at depth 13, code 74943, node 152229",
                "At remaining fuel 8 and original index 152229, selection on the full partial prefix of depth 13 and code 74943 returns the complete row with depth 13, base-four code 74943, original node 152229, kind 2, reserved field 0, 985 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18724-151266", "unmarked_context_12_18724_151266", "Unmarked parent at depth 12, code 18724",
                "The frontier Boolean is false at remaining fuel 9, original node 151266, the whole prefixCache at depth 12 and code 18724, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-18734-152163", "unmarked_context_12_18734_152163", "Unmarked parent at depth 12, code 18734",
                "The frontier Boolean is false at remaining fuel 9, original node 152163, the whole prefixCache at depth 12 and code 18734, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18724-151266", "node_context_12_18724_151266", "Original split at fuel 9 and node 151266",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 151215, 151241, 151261, 151265. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-18734-152163", "node_context_12_18734_152163", "Original split at fuel 9 and node 152163",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 152111, 152136, 152154, 152162. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-74897-151241", "context_13_74897_151241", "Context at depth 13, code 74897, node 151241",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 74897 and original node 151241, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-74943-152229", "context_13_74943_152229", "Context at depth 13, code 74943, node 152229",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 74943 and original node 152229, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
