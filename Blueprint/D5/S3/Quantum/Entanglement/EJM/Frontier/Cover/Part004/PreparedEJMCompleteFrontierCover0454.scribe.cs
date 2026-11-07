using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0454Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0454.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0454",
        H("Original frontier context coverage 0454"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21796", "selected_cut_21796", "Selected cut at depth 13, code 301180, node 557431",
                "At remaining fuel 8 and original index 557431, selection on the full partial prefix of depth 13 and code 301180 returns the complete row with depth 13, base-four code 301180, original node 557431, kind 2, reserved field 0, 1373 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21843", "selected_cut_21843", "Selected cut at depth 13, code 301239, node 558317",
                "At remaining fuel 8 and original index 558317, selection on the full partial prefix of depth 13 and code 301239 returns the complete row with depth 13, base-four code 301239, original node 558317, kind 2, reserved field 0, 773 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75294-557403", "unmarked_context_12_75294_557403", "Unmarked parent at depth 12, code 75294",
                "The frontier Boolean is false at remaining fuel 9, original node 557403, the whole prefixCache at depth 12 and code 75294, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75308-558253", "unmarked_context_12_75308_558253", "Unmarked parent at depth 12, code 75308",
                "The frontier Boolean is false at remaining fuel 9, original node 558253, the whole prefixCache at depth 12 and code 75308, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75294-557403", "node_context_12_75294_557403", "Original split at fuel 9 and node 557403",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 557353, 557381, 557396, 557402. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75308-558253", "node_context_12_75308_558253", "Original split at fuel 9 and node 558253",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 558145, 558201, 558242, 558252. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75294-557403", "context_12_75294_557403", "Context at depth 12, code 75294, node 557403",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75294 and original node 557403, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_301176_557353, context_13_301177_557381, context_13_301178_557396, context_13_301179_557402.", DescribeRole.Theorem),
            Node("context-13-301239-558317", "context_13_301239_558317", "Context at depth 13, code 301239, node 558317",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 301239 and original node 558317, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
