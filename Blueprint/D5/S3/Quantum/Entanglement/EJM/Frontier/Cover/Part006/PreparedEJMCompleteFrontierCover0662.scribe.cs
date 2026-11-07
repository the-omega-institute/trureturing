using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0662Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0662.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0662",
        H("Original frontier context coverage 0662"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31779", "selected_cut_31779", "Selected cut at depth 13, code 430152, node 815456",
                "At remaining fuel 8 and original index 815456, selection on the full partial prefix of depth 13 and code 430152 returns the complete row with depth 13, base-four code 430152, original node 815456, kind 2, reserved field 0, 1505 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31826", "selected_cut_31826", "Selected cut at depth 13, code 430217, node 816731",
                "At remaining fuel 8 and original index 816731, selection on the full partial prefix of depth 13 and code 430217 returns the complete row with depth 13, base-four code 430217, original node 816731, kind 2, reserved field 0, 1965 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-107537-815429", "unmarked_context_12_107537_815429", "Unmarked parent at depth 12, code 107537",
                "The frontier Boolean is false at remaining fuel 9, original node 815429, the whole prefixCache at depth 12 and code 107537, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-107553-816655", "unmarked_context_12_107553_816655", "Unmarked parent at depth 12, code 107553",
                "The frontier Boolean is false at remaining fuel 9, original node 816655, the whole prefixCache at depth 12 and code 107553, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-107537-815429", "node_context_12_107537_815429", "Original split at fuel 9 and node 815429",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 815370, 815400, 815420, 815428. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-107553-816655", "node_context_12_107553_816655", "Original split at fuel 9 and node 816655",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 816571, 816633, 816647, 816654. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-107537-815429", "context_12_107537_815429", "Context at depth 12, code 107537, node 815429",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 107537 and original node 815429, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_430148_815370, context_13_430149_815400, context_13_430150_815420, context_13_430151_815428.", DescribeRole.Theorem),
            Node("context-13-430217-816731", "context_13_430217_816731", "Context at depth 13, code 430217, node 816731",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 430217 and original node 816731, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
