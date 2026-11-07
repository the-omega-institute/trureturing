using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0220Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0220.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0220",
        H("Original frontier context coverage 0220"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10564", "selected_cut_10564", "Selected cut at depth 13, code 100540, node 286291",
                "At remaining fuel 8 and original index 286291, selection on the full partial prefix of depth 13 and code 100540 returns the complete row with depth 13, base-four code 100540, original node 286291, kind 2, reserved field 0, 753 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10610", "selected_cut_10610", "Selected cut at depth 13, code 100595, node 287086",
                "At remaining fuel 8 and original index 287086, selection on the full partial prefix of depth 13 and code 100595 returns the complete row with depth 13, base-four code 100595, original node 287086, kind 2, reserved field 0, 769 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25134-286280", "unmarked_context_12_25134_286280", "Unmarked parent at depth 12, code 25134",
                "The frontier Boolean is false at remaining fuel 9, original node 286280, the whole prefixCache at depth 12 and code 25134, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25148-287087", "unmarked_context_12_25148_287087", "Unmarked parent at depth 12, code 25148",
                "The frontier Boolean is false at remaining fuel 9, original node 287087, the whole prefixCache at depth 12 and code 25148, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25134-286280", "node_context_12_25134_286280", "Original split at fuel 9 and node 286280",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 286234, 286261, 286273, 286279. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25148-287087", "node_context_12_25148_287087", "Original split at fuel 9 and node 287087",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 287039, 287063, 287079, 287086. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25134-286280", "context_12_25134_286280", "Context at depth 12, code 25134, node 286280",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25134 and original node 286280, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_100536_286234, context_13_100537_286261, context_13_100538_286273, context_13_100539_286279.", DescribeRole.Theorem),
            Node("context-12-25148-287087", "context_12_25148_287087", "Context at depth 12, code 25148, node 287087",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25148 and original node 287087, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_100592_287039, context_13_100593_287063, context_13_100594_287079, context_13_100595_287086.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
