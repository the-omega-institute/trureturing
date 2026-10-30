using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0099Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0099.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0099",
        H("Original frontier context coverage 0099"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04756", "selected_cut_04756", "Selected cut at depth 13, code 74944, node 152243",
                "At remaining fuel 8 and original index 152243, selection on the full partial prefix of depth 13 and code 74944 returns the complete row with depth 13, base-four code 74944, original node 152243, kind 2, reserved field 0, 881 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04803", "selected_cut_04803", "Selected cut at depth 13, code 74991, node 153114",
                "At remaining fuel 8 and original index 153114, selection on the full partial prefix of depth 13 and code 74991 returns the complete row with depth 13, base-four code 74991, original node 153114, kind 2, reserved field 0, 1017 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18735-152230", "unmarked_context_12_18735_152230", "Unmarked parent at depth 12, code 18735",
                "The frontier Boolean is false at remaining fuel 9, original node 152230, the whole prefixCache at depth 12 and code 18735, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-18746-153029", "unmarked_context_12_18746_153029", "Unmarked parent at depth 12, code 18746",
                "The frontier Boolean is false at remaining fuel 9, original node 153029, the whole prefixCache at depth 12 and code 18746, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18735-152230", "node_context_12_18735_152230", "Original split at fuel 9 and node 152230",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 152179, 152203, 152223, 152229. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-18746-153029", "node_context_12_18746_153029", "Original split at fuel 9 and node 153029",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 152959, 152997, 153020, 153028. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-18735-152230", "context_12_18735_152230", "Context at depth 12, code 18735, node 152230",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18735 and original node 152230, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_74940_152179, context_13_74941_152203, context_13_74942_152223, context_13_74943_152229.", DescribeRole.Theorem),
            Node("context-13-74991-153114", "context_13_74991_153114", "Context at depth 13, code 74991, node 153114",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 74991 and original node 153114, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
