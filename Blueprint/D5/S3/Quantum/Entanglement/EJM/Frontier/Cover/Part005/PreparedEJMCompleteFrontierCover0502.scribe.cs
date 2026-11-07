using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0502Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0502.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0502",
        H("Original frontier context coverage 0502"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24099", "selected_cut_24099", "Selected cut at depth 12, code 76884, node 608798",
                "At remaining fuel 9 and original index 608798, selection on the full partial prefix of depth 12 and code 76884 returns the complete row with depth 12, base-four code 76884, original node 608798, kind 2, reserved field 0, 3849 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24146", "selected_cut_24146", "Selected cut at depth 12, code 76916, node 610435",
                "At remaining fuel 9 and original index 610435, selection on the full partial prefix of depth 12 and code 76916 returns the complete row with depth 12, base-four code 76916, original node 610435, kind 2, reserved field 0, 2961 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19220-608749", "unmarked_context_11_19220_608749", "Unmarked parent at depth 11, code 19220",
                "The frontier Boolean is false at remaining fuel 10, original node 608749, the whole prefixCache at depth 11 and code 19220, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19228-610396", "unmarked_context_11_19228_610396", "Unmarked parent at depth 11, code 19228",
                "The frontier Boolean is false at remaining fuel 10, original node 610396, the whole prefixCache at depth 11 and code 19228, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19220-608749", "node_context_11_19220_608749", "Original split at fuel 10 and node 608749",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 266170, 608648, 608699, 608748. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19228-610396", "node_context_11_19228_610396", "Original split at fuel 10 and node 610396",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 393180, 610295, 610343, 610395. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-19220-608749", "context_11_19220_608749", "Context at depth 11, code 19220, node 608749",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19220 and original node 608749, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_76880_266170, context_12_76881_608648, context_12_76882_608699, context_12_76883_608748.", DescribeRole.Theorem),
            Node("context-12-76916-610435", "context_12_76916_610435", "Context at depth 12, code 76916, node 610435",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76916 and original node 610435, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
