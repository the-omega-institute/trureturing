using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0146Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0146.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0146",
        H("Original frontier context coverage 0146"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07012", "selected_cut_07012", "Selected cut at depth 13, code 88252, node 206238",
                "At remaining fuel 8 and original index 206238, selection on the full partial prefix of depth 13 and code 88252 returns the complete row with depth 13, base-four code 88252, original node 206238, kind 2, reserved field 0, 565 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07059", "selected_cut_07059", "Selected cut at depth 13, code 88299, node 207058",
                "At remaining fuel 8 and original index 207058, selection on the full partial prefix of depth 13 and code 88299 returns the complete row with depth 13, base-four code 88299, original node 207058, kind 2, reserved field 0, 1185 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22062-206229", "unmarked_context_12_22062_206229", "Unmarked parent at depth 12, code 22062",
                "The frontier Boolean is false at remaining fuel 9, original node 206229, the whole prefixCache at depth 12 and code 22062, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22073-206938", "unmarked_context_12_22073_206938", "Unmarked parent at depth 12, code 22073",
                "The frontier Boolean is false at remaining fuel 9, original node 206938, the whole prefixCache at depth 12 and code 22073, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22062-206229", "node_context_12_22062_206229", "Original split at fuel 9 and node 206229",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 206182, 206211, 206223, 206228. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22073-206938", "node_context_12_22073_206938", "Original split at fuel 9 and node 206938",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 206884, 206913, 206931, 206937. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-22062-206229", "context_12_22062_206229", "Context at depth 12, code 22062, node 206229",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22062 and original node 206229, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_88248_206182, context_13_88249_206211, context_13_88250_206223, context_13_88251_206228.", DescribeRole.Theorem),
            Node("context-13-88299-207058", "context_13_88299_207058", "Context at depth 13, code 88299, node 207058",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88299 and original node 207058, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
