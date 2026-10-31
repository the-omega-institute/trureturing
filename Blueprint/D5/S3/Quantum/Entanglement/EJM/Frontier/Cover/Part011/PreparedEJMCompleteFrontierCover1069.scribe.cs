using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1069Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1069.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1069",
        H("Original frontier context coverage 1069"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51314", "selected_cut_51314", "Selected cut at depth 11, code 280712, node 1478834",
                "At remaining fuel 10 and original index 1478834, selection on the full partial prefix of depth 11 and code 280712 returns the complete row with depth 11, base-four code 280712, original node 1478834, kind 2, reserved field 0, 2397 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51362", "selected_cut_51362", "Selected cut at depth 11, code 280799, node 1470044",
                "At remaining fuel 10 and original index 1470044, selection on the full partial prefix of depth 11 and code 280799 returns the complete row with depth 11, base-four code 280799, original node 1470044, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-70178-1478909", "unmarked_context_10_70178_1478909", "Unmarked parent at depth 10, code 70178",
                "The frontier Boolean is false at remaining fuel 11, original node 1478909, the whole prefixCache at depth 10 and code 70178, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-70199-1480453", "unmarked_context_10_70199_1480453", "Unmarked parent at depth 10, code 70199",
                "The frontier Boolean is false at remaining fuel 11, original node 1480453, the whole prefixCache at depth 10 and code 70199, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-70178-1478909", "node_context_10_70178_1478909", "Original split at fuel 11 and node 1478909",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1478834, 1478873, 1468743, 1478908. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-70199-1480453", "node_context_10_70199_1480453", "Original split at fuel 11 and node 1480453",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1480375, 1480423, 1480452, 1470044. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-280712-1478834", "context_11_280712_1478834", "Context at depth 11, code 280712, node 1478834",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 280712 and original node 1478834, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-70199-1480453", "context_10_70199_1480453", "Context at depth 10, code 70199, node 1480453",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 70199 and original node 1480453, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_280796_1480375, context_11_280797_1480423, context_11_280798_1480452, context_11_280799_1470044.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
