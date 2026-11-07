using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0323Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0323.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0323",
        H("Original frontier context coverage 0323"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15507", "selected_cut_15507", "Selected cut at depth 13, code 111045, node 396930",
                "At remaining fuel 8 and original index 396930, selection on the full partial prefix of depth 13 and code 111045 returns the complete row with depth 13, base-four code 111045, original node 396930, kind 2, reserved field 0, 993 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15554", "selected_cut_15554", "Selected cut at depth 12, code 27800, node 398405",
                "At remaining fuel 9 and original index 398405, selection on the full partial prefix of depth 12 and code 27800 returns the complete row with depth 12, base-four code 27800, original node 398405, kind 2, reserved field 0, 2229 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27761-396968", "unmarked_context_12_27761_396968", "Unmarked parent at depth 12, code 27761",
                "The frontier Boolean is false at remaining fuel 9, original node 396968, the whole prefixCache at depth 12 and code 27761, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6949-398376", "unmarked_context_11_6949_398376", "Unmarked parent at depth 11, code 6949",
                "The frontier Boolean is false at remaining fuel 10, original node 398376, the whole prefixCache at depth 11 and code 6949, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27761-396968", "node_context_12_27761_396968", "Original split at fuel 9 and node 396968",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 396930, 396961, 396967. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6949-398376", "node_context_11_6949_398376", "Original split at fuel 10 and node 398376",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 398296, 398322, 398346, 398375. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-111045-396930", "context_13_111045_396930", "Context at depth 13, code 111045, node 396930",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111045 and original node 396930, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27800-398405", "context_12_27800_398405", "Context at depth 12, code 27800, node 398405",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27800 and original node 398405, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
