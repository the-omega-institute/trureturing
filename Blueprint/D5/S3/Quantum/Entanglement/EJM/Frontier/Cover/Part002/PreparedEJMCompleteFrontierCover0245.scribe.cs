using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0245Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0245.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0245",
        H("Original frontier context coverage 0245"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11762", "selected_cut_11762", "Selected cut at depth 14, code 413840, node 314758",
                "At remaining fuel 7 and original index 314758, selection on the full partial prefix of depth 14 and code 413840 returns the complete row with depth 14, base-four code 413840, original node 314758, kind 2, reserved field 0, 1137 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11809", "selected_cut_11809", "Selected cut at depth 13, code 103495, node 316014",
                "At remaining fuel 8 and original index 316014, selection on the full partial prefix of depth 13 and code 103495 returns the complete row with depth 13, base-four code 103495, original node 316014, kind 2, reserved field 0, 741 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-103460-314800", "unmarked_context_13_103460_314800", "Unmarked parent at depth 13, code 103460",
                "The frontier Boolean is false at remaining fuel 8, original node 314800, the whole prefixCache at depth 13 and code 103460, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25873-316015", "unmarked_context_12_25873_316015", "Unmarked parent at depth 12, code 25873",
                "The frontier Boolean is false at remaining fuel 9, original node 316015, the whole prefixCache at depth 12 and code 25873, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-103460-314800", "node_context_13_103460_314800", "Original split at fuel 8 and node 314800",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 314758, 314767, 314780, 314799. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25873-316015", "node_context_12_25873_316015", "Original split at fuel 9 and node 316015",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 315969, 315988, 316010, 316014. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-413840-314758", "context_14_413840_314758", "Context at depth 14, code 413840, node 314758",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 413840 and original node 314758, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25873-316015", "context_12_25873_316015", "Context at depth 12, code 25873, node 316015",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25873 and original node 316015, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_103492_315969, context_13_103493_315988, context_13_103494_316010, context_13_103495_316014.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
