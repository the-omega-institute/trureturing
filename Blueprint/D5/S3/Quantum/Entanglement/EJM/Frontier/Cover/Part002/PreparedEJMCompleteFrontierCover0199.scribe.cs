using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0199Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0199.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0199",
        H("Original frontier context coverage 0199"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09555", "selected_cut_09555", "Selected cut at depth 12, code 23448, node 263879",
                "At remaining fuel 9 and original index 263879, selection on the full partial prefix of depth 12 and code 23448 returns the complete row with depth 12, base-four code 23448, original node 263879, kind 2, reserved field 0, 2029 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09601", "selected_cut_09601", "Selected cut at depth 10, code 1471, node 265054",
                "At remaining fuel 11 and original index 265054, selection on the full partial prefix of depth 10 and code 1471 returns the complete row with depth 10, base-four code 1471, original node 265054, kind 2, reserved field 0, 1405 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5862-263953", "unmarked_context_11_5862_263953", "Unmarked parent at depth 11, code 5862",
                "The frontier Boolean is false at remaining fuel 10, original node 263953, the whole prefixCache at depth 11 and code 5862, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-91-265056", "unmarked_context_8_91_265056", "Unmarked parent at depth 8, code 91",
                "The frontier Boolean is false at remaining fuel 13, original node 265056, the whole prefixCache at depth 8 and code 91, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5862-263953", "node_context_11_5862_263953", "Original split at fuel 10 and node 263953",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 263879, 263908, 263930, 263952. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-91-265056", "node_context_8_91_265056", "Original split at fuel 13 and node 265056",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 257786, 263122, 264614, 265055. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-23448-263879", "context_12_23448_263879", "Context at depth 12, code 23448, node 263879",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23448 and original node 263879, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-8-91-265056", "context_8_91_265056", "Context at depth 8, code 91, node 265056",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 91 and original node 265056, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_9_364_257786, context_9_365_263122, context_9_366_264614, context_9_367_265055.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
