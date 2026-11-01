using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0482Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0482.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0482",
        H("Original frontier context coverage 0482"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23139", "selected_cut_23139", "Selected cut at depth 12, code 76170, node 585990",
                "At remaining fuel 9 and original index 585990, selection on the full partial prefix of depth 12 and code 76170 returns the complete row with depth 12, base-four code 76170, original node 585990, kind 2, reserved field 0, 2169 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23187", "selected_cut_23187", "Selected cut at depth 12, code 76221, node 586731",
                "At remaining fuel 9 and original index 586731, selection on the full partial prefix of depth 12 and code 76221 returns the complete row with depth 12, base-four code 76221, original node 586731, kind 2, reserved field 0, 1077 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19042-586013", "unmarked_context_11_19042_586013", "Unmarked parent at depth 11, code 19042",
                "The frontier Boolean is false at remaining fuel 10, original node 586013, the whole prefixCache at depth 11 and code 19042, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19054-586711", "unmarked_context_11_19054_586711", "Unmarked parent at depth 11, code 19054",
                "The frontier Boolean is false at remaining fuel 10, original node 586711, the whole prefixCache at depth 11 and code 19054, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19042-586013", "node_context_11_19042_586013", "Original split at fuel 10 and node 586013",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 585942, 585966, 585990, 586012. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19054-586711", "node_context_11_19054_586711", "Original split at fuel 10 and node 586711",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 586679, 586688, 586701, 586710. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76170-585990", "context_12_76170_585990", "Context at depth 12, code 76170, node 585990",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76170 and original node 585990, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-76221-586731", "context_12_76221_586731", "Context at depth 12, code 76221, node 586731",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76221 and original node 586731, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
