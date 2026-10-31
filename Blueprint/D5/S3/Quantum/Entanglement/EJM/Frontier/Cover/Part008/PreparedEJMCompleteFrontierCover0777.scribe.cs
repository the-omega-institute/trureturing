using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0777Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0777.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0777",
        H("Original frontier context coverage 0777"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37299", "selected_cut_37299", "Selected cut at depth 12, code 299574, node 996624",
                "At remaining fuel 9 and original index 996624, selection on the full partial prefix of depth 12 and code 299574 returns the complete row with depth 12, base-four code 299574, original node 996624, kind 2, reserved field 0, 3385 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37346", "selected_cut_37346", "Selected cut at depth 12, code 299639, node 998081",
                "At remaining fuel 9 and original index 998081, selection on the full partial prefix of depth 12 and code 299639 returns the complete row with depth 12, base-four code 299639, original node 998081, kind 2, reserved field 0, 1813 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-74893-996679", "unmarked_context_11_74893_996679", "Unmarked parent at depth 11, code 74893",
                "The frontier Boolean is false at remaining fuel 10, original node 996679, the whole prefixCache at depth 11 and code 74893, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-74909-998082", "unmarked_context_11_74909_998082", "Unmarked parent at depth 11, code 74909",
                "The frontier Boolean is false at remaining fuel 10, original node 998082, the whole prefixCache at depth 11 and code 74909, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-74893-996679", "node_context_11_74893_996679", "Original split at fuel 10 and node 996679",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 996510, 996576, 996624, 996678. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-74909-998082", "node_context_11_74909_998082", "Original split at fuel 10 and node 998082",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 998038, 691709, 998055, 998081. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-299574-996624", "context_12_299574_996624", "Context at depth 12, code 299574, node 996624",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299574 and original node 996624, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-74909-998082", "context_11_74909_998082", "Context at depth 11, code 74909, node 998082",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 74909 and original node 998082, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_299636_998038, context_12_299637_691709, context_12_299638_998055, context_12_299639_998081.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
