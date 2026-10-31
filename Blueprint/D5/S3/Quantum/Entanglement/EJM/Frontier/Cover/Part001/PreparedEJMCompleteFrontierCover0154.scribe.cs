using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0154Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0154.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0154",
        H("Original frontier context coverage 0154"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07395", "selected_cut_07395", "Selected cut at depth 13, code 90168, node 214955",
                "At remaining fuel 8 and original index 214955, selection on the full partial prefix of depth 13 and code 90168 returns the complete row with depth 13, base-four code 90168, original node 214955, kind 2, reserved field 0, 3281 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07441", "selected_cut_07441", "Selected cut at depth 13, code 90208, node 216201",
                "At remaining fuel 8 and original index 216201, selection on the full partial prefix of depth 13 and code 90208 returns the complete row with depth 13, base-four code 90208, original node 216201, kind 2, reserved field 0, 1053 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22541-214894", "unmarked_context_12_22541_214894", "Unmarked parent at depth 12, code 22541",
                "The frontier Boolean is false at remaining fuel 9, original node 214894, the whole prefixCache at depth 12 and code 22541, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5637-216186", "unmarked_context_11_5637_216186", "Unmarked parent at depth 11, code 5637",
                "The frontier Boolean is false at remaining fuel 10, original node 216186, the whole prefixCache at depth 11 and code 5637, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22541-214894", "node_context_12_22541_214894", "Original split at fuel 9 and node 214894",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 214806, 214859, 214882, 214893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5637-216186", "node_context_11_5637_216186", "Original split at fuel 10 and node 216186",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 215929, 216006, 216101, 216185. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-22541-214894", "context_12_22541_214894", "Context at depth 12, code 22541, node 214894",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22541 and original node 214894, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_90164_214806, context_13_90165_214859, context_13_90166_214882, context_13_90167_214893.", DescribeRole.Theorem),
            Node("context-13-90208-216201", "context_13_90208_216201", "Context at depth 13, code 90208, node 216201",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90208 and original node 216201, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
