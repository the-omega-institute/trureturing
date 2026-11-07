using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0359Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0359.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0359",
        H("Original frontier context coverage 0359"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17234", "selected_cut_17234", "Selected cut at depth 12, code 69896, node 895",
                "At remaining fuel 9 and original index 895, selection on the full partial prefix of depth 12 and code 69896 returns the complete row with depth 12, base-four code 69896, original node 895, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17281", "selected_cut_17281", "Selected cut at depth 13, code 279685, node 439685",
                "At remaining fuel 8 and original index 439685, selection on the full partial prefix of depth 13 and code 279685 returns the complete row with depth 13, base-four code 279685, original node 439685, kind 2, reserved field 0, 1481 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-17473-438509", "unmarked_context_11_17473_438509", "Unmarked parent at depth 11, code 17473",
                "The frontier Boolean is false at remaining fuel 10, original node 438509, the whole prefixCache at depth 11 and code 17473, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4369-439627", "unmarked_context_10_4369_439627", "Unmarked parent at depth 10, code 4369",
                "The frontier Boolean is false at remaining fuel 11, original node 439627, the whole prefixCache at depth 10 and code 4369, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-17473-438509", "node_context_11_17473_438509", "Original split at fuel 10 and node 438509",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 895, 438290, 438508, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4369-439627", "node_context_10_4369_439627", "Original split at fuel 11 and node 439627",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 438992, 439171, 439626, 1736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-17473-438509", "context_11_17473_438509", "Context at depth 11, code 17473, node 438509",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 17473 and original node 438509, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_69892_895, context_12_69893_438290, context_12_69894_438508, context_12_69895_893.", DescribeRole.Theorem),
            Node("context-13-279685-439685", "context_13_279685_439685", "Context at depth 13, code 279685, node 439685",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 279685 and original node 439685, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
