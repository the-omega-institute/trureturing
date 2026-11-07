using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1081Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1081.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1081",
        H("Original frontier context coverage 1081"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51891", "selected_cut_51891", "Selected cut at depth 10, code 71307, node 1501573",
                "At remaining fuel 11 and original index 1501573, selection on the full partial prefix of depth 10 and code 71307 returns the complete row with depth 10, base-four code 71307, original node 1501573, kind 2, reserved field 0, 2197 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51937", "selected_cut_51937", "Selected cut at depth 9, code 17839, node 1503608",
                "At remaining fuel 12 and original index 1503608, selection on the full partial prefix of depth 9 and code 17839 returns the complete row with depth 9, base-four code 17839, original node 1503608, kind 2, reserved field 0, 2381 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-17826-1501574", "unmarked_context_9_17826_1501574", "Unmarked parent at depth 9, code 17826",
                "The frontier Boolean is false at remaining fuel 12, original node 1501574, the whole prefixCache at depth 9 and code 17826, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-7-1114-1503610", "unmarked_context_7_1114_1503610", "Unmarked parent at depth 7, code 1114",
                "The frontier Boolean is false at remaining fuel 14, original node 1503610, the whole prefixCache at depth 7 and code 1114, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-17826-1501574", "node_context_9_17826_1501574", "Original split at fuel 12 and node 1501574",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1501476, 1501534, 1469103, 1501573. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-7-1114-1503610", "node_context_7_1114_1503610", "Original split at fuel 14 and node 1503610",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 1501636, 1502489, 1502490, 1503609. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-71307-1501573", "context_10_71307_1501573", "Context at depth 10, code 71307, node 1501573",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 71307 and original node 1501573, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-7-1114-1503610", "context_7_1114_1503610", "Context at depth 7, code 1114, node 1503610",
                "The conclusion is adaptive Accepted at the exact depth 7, full base-four code 1114 and original node 1503610, hence remaining fuel 14, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_8_4456_1501636, context_8_4457_1502489, context_8_4458_1502490, context_8_4459_1503609.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
