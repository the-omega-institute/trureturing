using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0046Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0046.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0046",
        H("Original frontier context coverage 0046"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02211", "selected_cut_02211", "Selected cut at depth 14, code 90288, node 72960",
                "At remaining fuel 7 and original index 72960, selection on the full partial prefix of depth 14 and code 90288 returns the complete row with depth 14, base-four code 90288, original node 72960, kind 2, reserved field 0, 653 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02257", "selected_cut_02257", "Selected cut at depth 13, code 22594, node 74040",
                "At remaining fuel 8 and original index 74040, selection on the full partial prefix of depth 13 and code 22594 returns the complete row with depth 13, base-four code 22594, original node 74040, kind 2, reserved field 0, 2373 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5642-72950", "unmarked_context_12_5642_72950", "Unmarked parent at depth 12, code 5642",
                "The frontier Boolean is false at remaining fuel 9, original node 72950, the whole prefixCache at depth 12 and code 5642, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-352-73943", "unmarked_context_10_352_73943", "Unmarked parent at depth 10, code 352",
                "The frontier Boolean is false at remaining fuel 11, original node 73943, the whole prefixCache at depth 10 and code 352, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5642-72950", "node_context_12_5642_72950", "Original split at fuel 9 and node 72950",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 72701, 72816, 72890, 72949. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-352-73943", "node_context_10_352_73943", "Original split at fuel 11 and node 73943",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 71118, 72000, 73153, 73942. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-5642-72950", "context_12_5642_72950", "Context at depth 12, code 5642, node 72950",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5642 and original node 72950, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_22568_72701, context_13_22569_72816, context_13_22570_72890, context_13_22571_72949.", DescribeRole.Theorem),
            Node("context-13-22594-74040", "context_13_22594_74040", "Context at depth 13, code 22594, node 74040",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22594 and original node 74040, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
