using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0987Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0987.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0987",
        H("Original frontier context coverage 0987"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47379", "selected_cut_47379", "Selected cut at depth 11, code 93282, node 1325710",
                "At remaining fuel 10 and original index 1325710, selection on the full partial prefix of depth 11 and code 93282 returns the complete row with depth 11, base-four code 93282, original node 1325710, kind 2, reserved field 0, 3061 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47426", "selected_cut_47426", "Selected cut at depth 12, code 373295, node 265052",
                "At remaining fuel 9 and original index 265052, selection on the full partial prefix of depth 12 and code 373295 returns the complete row with depth 12, base-four code 373295, original node 265052, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23320-1325748", "unmarked_context_10_23320_1325748", "Unmarked parent at depth 10, code 23320",
                "The frontier Boolean is false at remaining fuel 11, original node 1325748, the whole prefixCache at depth 10 and code 23320, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23330-1327231", "unmarked_context_10_23330_1327231", "Unmarked parent at depth 10, code 23330",
                "The frontier Boolean is false at remaining fuel 11, original node 1327231, the whole prefixCache at depth 10 and code 23330, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23320-1325748", "node_context_10_23320_1325748", "Original split at fuel 11 and node 1325748",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 1325664, 1325710, 1325747. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23330-1327231", "node_context_10_23330_1327231", "Original split at fuel 11 and node 1327231",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1326962, 1327067, 1327068, 1327230. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-93282-1325710", "context_11_93282_1325710", "Context at depth 11, code 93282, node 1325710",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93282 and original node 1325710, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-23330-1327231", "context_10_23330_1327231", "Context at depth 10, code 23330, node 1327231",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23330 and original node 1327231, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_93320_1326962, context_11_93321_1327067, context_11_93322_1327068, context_11_93323_1327230.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
