using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0340Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0340.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0340",
        H("Original frontier context coverage 0340"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16324", "selected_cut_16324", "Selected cut at depth 13, code 112846, node 415737",
                "At remaining fuel 8 and original index 415737, selection on the full partial prefix of depth 13 and code 112846 returns the complete row with depth 13, base-four code 112846, original node 415737, kind 2, reserved field 0, 1729 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16370", "selected_cut_16370", "Selected cut at depth 12, code 28223, node 416574",
                "At remaining fuel 9 and original index 416574, selection on the full partial prefix of depth 12 and code 28223 returns the complete row with depth 12, base-four code 28223, original node 416574, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28211-415744", "unmarked_context_12_28211_415744", "Unmarked parent at depth 12, code 28211",
                "The frontier Boolean is false at remaining fuel 9, original node 415744, the whole prefixCache at depth 12 and code 28211, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1763-416576", "unmarked_context_10_1763_416576", "Unmarked parent at depth 10, code 1763",
                "The frontier Boolean is false at remaining fuel 11, original node 416576, the whole prefixCache at depth 10 and code 1763, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28211-415744", "node_context_12_28211_415744", "Original split at fuel 9 and node 415744",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 415664, 415713, 415737, 415743. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1763-416576", "node_context_10_1763_416576", "Original split at fuel 11 and node 416576",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 415745, 415974, 416288, 416575. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-112846-415737", "context_13_112846_415737", "Context at depth 13, code 112846, node 415737",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112846 and original node 415737, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-1763-416576", "context_10_1763_416576", "Context at depth 10, code 1763, node 416576",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1763 and original node 416576, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_7052_415745, context_11_7053_415974, context_11_7054_416288, context_11_7055_416575.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
