using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0485Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0485.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0485",
        H("Original frontier context coverage 0485"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23284", "selected_cut_23284", "Selected cut at depth 13, code 305278, node 589636",
                "At remaining fuel 8 and original index 589636, selection on the full partial prefix of depth 13 and code 305278 returns the complete row with depth 13, base-four code 305278, original node 589636, kind 2, reserved field 0, 1429 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23330", "selected_cut_23330", "Selected cut at depth 13, code 305351, node 590667",
                "At remaining fuel 8 and original index 590667, selection on the full partial prefix of depth 13 and code 305351 returns the complete row with depth 13, base-four code 305351, original node 590667, kind 2, reserved field 0, 1033 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76319-589648", "unmarked_context_12_76319_589648", "Unmarked parent at depth 12, code 76319",
                "The frontier Boolean is false at remaining fuel 9, original node 589648, the whole prefixCache at depth 12 and code 76319, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76337-590668", "unmarked_context_12_76337_590668", "Unmarked parent at depth 12, code 76337",
                "The frontier Boolean is false at remaining fuel 9, original node 590668, the whole prefixCache at depth 12 and code 76337, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76319-589648", "node_context_12_76319_589648", "Original split at fuel 9 and node 589648",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 589581, 589618, 589636, 589647. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76337-590668", "node_context_12_76337_590668", "Original split at fuel 9 and node 590668",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 590606, 590638, 590655, 590667. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-305278-589636", "context_13_305278_589636", "Context at depth 13, code 305278, node 589636",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 305278 and original node 589636, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-76337-590668", "context_12_76337_590668", "Context at depth 12, code 76337, node 590668",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76337 and original node 590668, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_305348_590606, context_13_305349_590638, context_13_305350_590655, context_13_305351_590667.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
