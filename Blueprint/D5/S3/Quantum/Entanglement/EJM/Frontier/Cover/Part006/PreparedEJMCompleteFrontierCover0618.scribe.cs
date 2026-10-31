using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0618Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0618.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0618",
        H("Original frontier context coverage 0618"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29667", "selected_cut_29667", "Selected cut at depth 13, code 374916, node 749066",
                "At remaining fuel 8 and original index 749066, selection on the full partial prefix of depth 13 and code 374916 returns the complete row with depth 13, base-four code 374916, original node 749066, kind 2, reserved field 0, 1277 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29715", "selected_cut_29715", "Selected cut at depth 13, code 374967, node 749851",
                "At remaining fuel 8 and original index 749851, selection on the full partial prefix of depth 13 and code 374967 returns the complete row with depth 13, base-four code 374967, original node 749851, kind 2, reserved field 0, 705 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93729-749124", "unmarked_context_12_93729_749124", "Unmarked parent at depth 12, code 93729",
                "The frontier Boolean is false at remaining fuel 9, original node 749124, the whole prefixCache at depth 12 and code 93729, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93741-749852", "unmarked_context_12_93741_749852", "Unmarked parent at depth 12, code 93741",
                "The frontier Boolean is false at remaining fuel 9, original node 749852, the whole prefixCache at depth 12 and code 93741, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93729-749124", "node_context_12_93729_749124", "Original split at fuel 9 and node 749124",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 749066, 749094, 749113, 749123. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93741-749852", "node_context_12_93741_749852", "Original split at fuel 9 and node 749852",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 749801, 749826, 749843, 749851. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-374916-749066", "context_13_374916_749066", "Context at depth 13, code 374916, node 749066",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 374916 and original node 749066, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93741-749852", "context_12_93741_749852", "Context at depth 12, code 93741, node 749852",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93741 and original node 749852, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_374964_749801, context_13_374965_749826, context_13_374966_749843, context_13_374967_749851.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
