using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0399Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0399.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0399",
        H("Original frontier context coverage 0399"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19156", "selected_cut_19156", "Selected cut at depth 13, code 288112, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 288112 returns the complete row with depth 13, base-four code 288112, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19202", "selected_cut_19202", "Selected cut at depth 13, code 288161, node 490920",
                "At remaining fuel 8 and original index 490920, selection on the full partial prefix of depth 13 and code 288161 returns the complete row with depth 13, base-four code 288161, original node 490920, kind 2, reserved field 0, 1753 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72027-490140", "unmarked_context_12_72027_490140", "Unmarked parent at depth 12, code 72027",
                "The frontier Boolean is false at remaining fuel 9, original node 490140, the whole prefixCache at depth 12 and code 72027, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18009-490888", "unmarked_context_11_18009_490888", "Unmarked parent at depth 11, code 18009",
                "The frontier Boolean is false at remaining fuel 10, original node 490888, the whole prefixCache at depth 11 and code 18009, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72027-490140", "node_context_12_72027_490140", "Original split at fuel 9 and node 490140",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 490095, 490126, 490139. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18009-490888", "node_context_11_18009_490888", "Original split at fuel 10 and node 490888",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 490747, 441672, 490823, 490887. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-72027-490140", "context_12_72027_490140", "Context at depth 12, code 72027, node 490140",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72027 and original node 490140, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_288108_3444, context_13_288109_490095, context_13_288110_490126, context_13_288111_490139.", DescribeRole.Theorem),
            Node("context-13-288161-490920", "context_13_288161_490920", "Context at depth 13, code 288161, node 490920",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288161 and original node 490920, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
