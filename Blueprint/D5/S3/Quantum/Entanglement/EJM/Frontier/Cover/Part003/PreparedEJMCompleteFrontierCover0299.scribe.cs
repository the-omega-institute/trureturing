using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0299Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0299.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0299",
        H("Original frontier context coverage 0299"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14356", "selected_cut_14356", "Selected cut at depth 13, code 108748, node 371437",
                "At remaining fuel 8 and original index 371437, selection on the full partial prefix of depth 13 and code 108748 returns the complete row with depth 13, base-four code 108748, original node 371437, kind 2, reserved field 0, 953 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14403", "selected_cut_14403", "Selected cut at depth 13, code 108795, node 372170",
                "At remaining fuel 8 and original index 372170, selection on the full partial prefix of depth 13 and code 108795 returns the complete row with depth 13, base-four code 108795, original node 372170, kind 2, reserved field 0, 793 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27186-371422", "unmarked_context_12_27186_371422", "Unmarked parent at depth 12, code 27186",
                "The frontier Boolean is false at remaining fuel 9, original node 371422, the whole prefixCache at depth 12 and code 27186, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27198-372171", "unmarked_context_12_27198_372171", "Unmarked parent at depth 12, code 27198",
                "The frontier Boolean is false at remaining fuel 9, original node 372171, the whole prefixCache at depth 12 and code 27198, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27186-371422", "node_context_12_27186_371422", "Original split at fuel 9 and node 371422",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 371376, 371398, 371416, 371421. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27198-372171", "node_context_12_27198_372171", "Original split at fuel 9 and node 372171",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 372120, 372144, 372162, 372170. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-27186-371422", "context_12_27186_371422", "Context at depth 12, code 27186, node 371422",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27186 and original node 371422, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_108744_371376, context_13_108745_371398, context_13_108746_371416, context_13_108747_371421.", DescribeRole.Theorem),
            Node("context-12-27198-372171", "context_12_27198_372171", "Context at depth 12, code 27198, node 372171",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27198 and original node 372171, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_108792_372120, context_13_108793_372144, context_13_108794_372162, context_13_108795_372170.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
