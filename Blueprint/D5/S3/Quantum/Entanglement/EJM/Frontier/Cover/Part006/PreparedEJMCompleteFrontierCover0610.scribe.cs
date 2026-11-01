using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0610Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0610.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0610",
        H("Original frontier context coverage 0610"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29283", "selected_cut_29283", "Selected cut at depth 13, code 373860, node 739954",
                "At remaining fuel 8 and original index 739954, selection on the full partial prefix of depth 13 and code 373860 returns the complete row with depth 13, base-four code 373860, original node 739954, kind 2, reserved field 0, 1361 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29330", "selected_cut_29330", "Selected cut at depth 13, code 373907, node 740907",
                "At remaining fuel 8 and original index 740907, selection on the full partial prefix of depth 13 and code 373907 returns the complete row with depth 13, base-four code 373907, original node 740907, kind 2, reserved field 0, 797 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93465-740006", "unmarked_context_12_93465_740006", "Unmarked parent at depth 12, code 93465",
                "The frontier Boolean is false at remaining fuel 9, original node 740006, the whole prefixCache at depth 12 and code 93465, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93476-740908", "unmarked_context_12_93476_740908", "Unmarked parent at depth 12, code 93476",
                "The frontier Boolean is false at remaining fuel 9, original node 740908, the whole prefixCache at depth 12 and code 93476, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93465-740006", "node_context_12_93465_740006", "Original split at fuel 9 and node 740006",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 739954, 739973, 739996, 740005. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93476-740908", "node_context_12_93476_740908", "Original split at fuel 9 and node 740908",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 740855, 740878, 740900, 740907. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-373860-739954", "context_13_373860_739954", "Context at depth 13, code 373860, node 739954",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 373860 and original node 739954, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93476-740908", "context_12_93476_740908", "Context at depth 12, code 93476, node 740908",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93476 and original node 740908, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_373904_740855, context_13_373905_740878, context_13_373906_740900, context_13_373907_740907.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
