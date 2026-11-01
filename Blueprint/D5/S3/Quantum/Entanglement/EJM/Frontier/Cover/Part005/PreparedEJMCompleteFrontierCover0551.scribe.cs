using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0551Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0551.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0551",
        H("Original frontier context coverage 0551"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26451", "selected_cut_26451", "Selected cut at depth 13, code 355425, node 669414",
                "At remaining fuel 8 and original index 669414, selection on the full partial prefix of depth 13 and code 355425 returns the complete row with depth 13, base-four code 355425, original node 669414, kind 2, reserved field 0, 2177 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26498", "selected_cut_26498", "Selected cut at depth 13, code 355472, node 670472",
                "At remaining fuel 8 and original index 670472, selection on the full partial prefix of depth 13 and code 355472 returns the complete row with depth 13, base-four code 355472, original node 670472, kind 2, reserved field 0, 1145 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88856-669442", "unmarked_context_12_88856_669442", "Unmarked parent at depth 12, code 88856",
                "The frontier Boolean is false at remaining fuel 9, original node 669442, the whole prefixCache at depth 12 and code 88856, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22216-670459", "unmarked_context_11_22216_670459", "Unmarked parent at depth 11, code 22216",
                "The frontier Boolean is false at remaining fuel 10, original node 670459, the whole prefixCache at depth 11 and code 22216, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88856-669442", "node_context_12_88856_669442", "Original split at fuel 9 and node 669442",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 669383, 669414, 669436, 669441. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22216-670459", "node_context_11_22216_670459", "Original split at fuel 10 and node 670459",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 670242, 670306, 670398, 670458. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-355425-669414", "context_13_355425_669414", "Context at depth 13, code 355425, node 669414",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 355425 and original node 669414, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-355472-670472", "context_13_355472_670472", "Context at depth 13, code 355472, node 670472",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 355472 and original node 670472, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
