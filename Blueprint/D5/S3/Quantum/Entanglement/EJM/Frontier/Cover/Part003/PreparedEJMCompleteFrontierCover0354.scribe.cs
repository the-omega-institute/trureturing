using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0354Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0354.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0354",
        H("Original frontier context coverage 0354"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16996", "selected_cut_16996", "Selected cut at depth 13, code 114085, node 431922",
                "At remaining fuel 8 and original index 431922, selection on the full partial prefix of depth 13 and code 114085 returns the complete row with depth 13, base-four code 114085, original node 431922, kind 2, reserved field 0, 1481 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17043", "selected_cut_17043", "Selected cut at depth 12, code 28551, node 433278",
                "At remaining fuel 9 and original index 433278, selection on the full partial prefix of depth 12 and code 28551 returns the complete row with depth 12, base-four code 28551, original node 433278, kind 2, reserved field 0, 3117 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28521-431993", "unmarked_context_12_28521_431993", "Unmarked parent at depth 12, code 28521",
                "The frontier Boolean is false at remaining fuel 9, original node 431993, the whole prefixCache at depth 12 and code 28521, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-7136-433152", "unmarked_context_11_7136_433152", "Unmarked parent at depth 11, code 7136",
                "The frontier Boolean is false at remaining fuel 10, original node 433152, the whole prefixCache at depth 11 and code 7136, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28521-431993", "node_context_12_28521_431993", "Original split at fuel 9 and node 431993",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 431922, 431969, 431992. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-7136-433152", "node_context_11_7136_433152", "Original split at fuel 10 and node 433152",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 433052, 433089, 433119, 433151. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-114085-431922", "context_13_114085_431922", "Context at depth 13, code 114085, node 431922",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 114085 and original node 431922, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-28551-433278", "context_12_28551_433278", "Context at depth 12, code 28551, node 433278",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28551 and original node 433278, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
