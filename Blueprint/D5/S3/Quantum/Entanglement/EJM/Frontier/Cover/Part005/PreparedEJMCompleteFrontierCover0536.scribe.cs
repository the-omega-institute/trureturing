using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0536Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0536.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0536",
        H("Original frontier context coverage 0536"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25731", "selected_cut_25731", "Selected cut at depth 13, code 352404, node 652045",
                "At remaining fuel 8 and original index 652045, selection on the full partial prefix of depth 13 and code 352404 returns the complete row with depth 13, base-four code 352404, original node 652045, kind 2, reserved field 0, 949 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25778", "selected_cut_25778", "Selected cut at depth 13, code 352460, node 652965",
                "At remaining fuel 8 and original index 652965, selection on the full partial prefix of depth 13 and code 352460 returns the complete row with depth 13, base-four code 352460, original node 652965, kind 2, reserved field 0, 653 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88100-652031", "unmarked_context_12_88100_652031", "Unmarked parent at depth 12, code 88100",
                "The frontier Boolean is false at remaining fuel 9, original node 652031, the whole prefixCache at depth 12 and code 88100, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-88114-652949", "unmarked_context_12_88114_652949", "Unmarked parent at depth 12, code 88114",
                "The frontier Boolean is false at remaining fuel 9, original node 652949, the whole prefixCache at depth 12 and code 88114, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88100-652031", "node_context_12_88100_652031", "Original split at fuel 9 and node 652031",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 651962, 652008, 652025, 652030. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-88114-652949", "node_context_12_88114_652949", "Original split at fuel 9 and node 652949",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 652896, 652920, 652942, 652948. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-88100-652031", "context_12_88100_652031", "Context at depth 12, code 88100, node 652031",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88100 and original node 652031, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_352400_651962, context_13_352401_652008, context_13_352402_652025, context_13_352403_652030.", DescribeRole.Theorem),
            Node("context-13-352460-652965", "context_13_352460_652965", "Context at depth 13, code 352460, node 652965",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 352460 and original node 652965, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
