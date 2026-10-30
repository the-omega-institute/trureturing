using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0316Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0316.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0316",
        H("Original frontier context coverage 0316"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15171", "selected_cut_15171", "Selected cut at depth 13, code 110649, node 390674",
                "At remaining fuel 8 and original index 390674, selection on the full partial prefix of depth 13 and code 110649 returns the complete row with depth 13, base-four code 110649, original node 390674, kind 2, reserved field 0, 3693 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15218", "selected_cut_15218", "Selected cut at depth 13, code 110699, node 391679",
                "At remaining fuel 8 and original index 391679, selection on the full partial prefix of depth 13 and code 110699 returns the complete row with depth 13, base-four code 110699, original node 391679, kind 2, reserved field 0, 921 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27662-390710", "unmarked_context_12_27662_390710", "Unmarked parent at depth 12, code 27662",
                "The frontier Boolean is false at remaining fuel 9, original node 390710, the whole prefixCache at depth 12 and code 27662, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27674-391680", "unmarked_context_12_27674_391680", "Unmarked parent at depth 12, code 27674",
                "The frontier Boolean is false at remaining fuel 9, original node 391680, the whole prefixCache at depth 12 and code 27674, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27662-390710", "node_context_12_27662_390710", "Original split at fuel 9 and node 390710",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 390617, 390674, 390699, 390709. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27674-391680", "node_context_12_27674_391680", "Original split at fuel 9 and node 391680",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 391619, 391655, 391672, 391679. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-110649-390674", "context_13_110649_390674", "Context at depth 13, code 110649, node 390674",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 110649 and original node 390674, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27674-391680", "context_12_27674_391680", "Context at depth 12, code 27674, node 391680",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27674 and original node 391680, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_110696_391619, context_13_110697_391655, context_13_110698_391672, context_13_110699_391679.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
