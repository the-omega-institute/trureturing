using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0477Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0477.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0477",
        H("Original frontier context coverage 0477"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22899", "selected_cut_22899", "Selected cut at depth 13, code 304236, node 581289",
                "At remaining fuel 8 and original index 581289, selection on the full partial prefix of depth 13 and code 304236 returns the complete row with depth 13, base-four code 304236, original node 581289, kind 2, reserved field 0, 1513 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22946", "selected_cut_22946", "Selected cut at depth 13, code 304295, node 582106",
                "At remaining fuel 8 and original index 582106, selection on the full partial prefix of depth 13 and code 304295 returns the complete row with depth 13, base-four code 304295, original node 582106, kind 2, reserved field 0, 1097 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76059-581336", "unmarked_context_12_76059_581336", "Unmarked parent at depth 12, code 76059",
                "The frontier Boolean is false at remaining fuel 9, original node 581336, the whole prefixCache at depth 12 and code 76059, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76073-582107", "unmarked_context_12_76073_582107", "Unmarked parent at depth 12, code 76073",
                "The frontier Boolean is false at remaining fuel 9, original node 582107, the whole prefixCache at depth 12 and code 76073, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76059-581336", "node_context_12_76059_581336", "Original split at fuel 9 and node 581336",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 581289, 581312, 581331, 581335. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76073-582107", "node_context_12_76073_582107", "Original split at fuel 9 and node 582107",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 582060, 582084, 582101, 582106. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-304236-581289", "context_13_304236_581289", "Context at depth 13, code 304236, node 581289",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 304236 and original node 581289, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-76073-582107", "context_12_76073_582107", "Context at depth 12, code 76073, node 582107",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76073 and original node 582107, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_304292_582060, context_13_304293_582084, context_13_304294_582101, context_13_304295_582106.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
