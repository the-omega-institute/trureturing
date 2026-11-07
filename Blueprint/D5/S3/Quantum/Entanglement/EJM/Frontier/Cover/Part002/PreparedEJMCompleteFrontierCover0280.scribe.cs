using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0280Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0280.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0280",
        H("Original frontier context coverage 0280"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13443", "selected_cut_13443", "Selected cut at depth 13, code 106782, node 352989",
                "At remaining fuel 8 and original index 352989, selection on the full partial prefix of depth 13 and code 106782 returns the complete row with depth 13, base-four code 106782, original node 352989, kind 2, reserved field 0, 1565 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13489", "selected_cut_13489", "Selected cut at depth 13, code 106831, node 353739",
                "At remaining fuel 8 and original index 353739, selection on the full partial prefix of depth 13 and code 106831 returns the complete row with depth 13, base-four code 106831, original node 353739, kind 2, reserved field 0, 893 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26695-353001", "unmarked_context_12_26695_353001", "Unmarked parent at depth 12, code 26695",
                "The frontier Boolean is false at remaining fuel 9, original node 353001, the whole prefixCache at depth 12 and code 26695, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6676-353741", "unmarked_context_11_6676_353741", "Unmarked parent at depth 11, code 6676",
                "The frontier Boolean is false at remaining fuel 10, original node 353741, the whole prefixCache at depth 11 and code 6676, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26695-353001", "node_context_12_26695_353001", "Original split at fuel 9 and node 353001",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 352969, 352989, 353000. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6676-353741", "node_context_11_6676_353741", "Original split at fuel 10 and node 353741",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 353635, 170504, 353685, 353740. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-106782-352989", "context_13_106782_352989", "Context at depth 13, code 106782, node 352989",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106782 and original node 352989, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-6676-353741", "context_11_6676_353741", "Context at depth 11, code 6676, node 353741",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6676 and original node 353741, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_26704_353635, context_12_26705_170504, context_12_26706_353685, context_12_26707_353740.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
