using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0193Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0193.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0193",
        H("Original frontier context coverage 0193"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09269", "selected_cut_09269", "Selected cut at depth 13, code 93374, node 256464",
                "At remaining fuel 8 and original index 256464, selection on the full partial prefix of depth 13 and code 93374 returns the complete row with depth 13, base-four code 93374, original node 256464, kind 2, reserved field 0, 2233 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09315", "selected_cut_09315", "Selected cut at depth 13, code 93420, node 257381",
                "At remaining fuel 8 and original index 257381, selection on the full partial prefix of depth 13 and code 93420 returns the complete row with depth 13, base-four code 93420, original node 257381, kind 2, reserved field 0, 197 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-93373-256432", "unmarked_context_13_93373_256432", "Unmarked parent at depth 13, code 93373",
                "The frontier Boolean is false at remaining fuel 8, original node 256432, the whole prefixCache at depth 13 and code 93373, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23354-257377", "unmarked_context_12_23354_257377", "Unmarked parent at depth 12, code 23354",
                "The frontier Boolean is false at remaining fuel 9, original node 257377, the whole prefixCache at depth 12 and code 23354, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-93373-256432", "node_context_13_93373_256432", "Original split at fuel 8 and node 256432",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 256367, 256394, 256416, 256431. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23354-257377", "node_context_12_23354_257377", "Original split at fuel 9 and node 257377",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 257277, 257325, 257366, 257376. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-93373-256432", "context_13_93373_256432", "Context at depth 13, code 93373, node 256432",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93373 and original node 256432, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_373492_256367, context_14_373493_256394, context_14_373494_256416, context_14_373495_256431.", DescribeRole.Theorem),
            Node("context-13-93420-257381", "context_13_93420_257381", "Context at depth 13, code 93420, node 257381",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93420 and original node 257381, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
