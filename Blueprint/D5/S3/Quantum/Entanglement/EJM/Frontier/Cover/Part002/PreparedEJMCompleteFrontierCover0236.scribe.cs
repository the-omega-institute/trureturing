using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0236Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0236.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0236",
        H("Original frontier context coverage 0236"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11331", "selected_cut_11331", "Selected cut at depth 13, code 102480, node 304059",
                "At remaining fuel 8 and original index 304059, selection on the full partial prefix of depth 13 and code 102480 returns the complete row with depth 13, base-four code 102480, original node 304059, kind 2, reserved field 0, 1601 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11377", "selected_cut_11377", "Selected cut at depth 13, code 102532, node 305163",
                "At remaining fuel 8 and original index 305163, selection on the full partial prefix of depth 13 and code 102532 returns the complete row with depth 13, base-four code 102532, original node 305163, kind 2, reserved field 0, 961 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25619-304034", "unmarked_context_12_25619_304034", "Unmarked parent at depth 12, code 25619",
                "The frontier Boolean is false at remaining fuel 9, original node 304034, the whole prefixCache at depth 12 and code 25619, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25632-305150", "unmarked_context_12_25632_305150", "Unmarked parent at depth 12, code 25632",
                "The frontier Boolean is false at remaining fuel 9, original node 305150, the whole prefixCache at depth 12 and code 25632, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25619-304034", "node_context_12_25619_304034", "Original split at fuel 9 and node 304034",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 303975, 304003, 304025, 304033. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25632-305150", "node_context_12_25632_305150", "Original split at fuel 9 and node 305150",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 305030, 305094, 305131, 305149. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25619-304034", "context_12_25619_304034", "Context at depth 12, code 25619, node 304034",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25619 and original node 304034, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_102476_303975, context_13_102477_304003, context_13_102478_304025, context_13_102479_304033.", DescribeRole.Theorem),
            Node("context-13-102532-305163", "context_13_102532_305163", "Context at depth 13, code 102532, node 305163",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 102532 and original node 305163, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
