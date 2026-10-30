using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0117Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0117.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0117",
        H("Original frontier context coverage 0117"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05619", "selected_cut_05619", "Selected cut at depth 11, code 5187, node 1736",
                "At remaining fuel 10 and original index 1736, selection on the full partial prefix of depth 11 and code 5187 returns the complete row with depth 11, base-four code 5187, original node 1736, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05666", "selected_cut_05666", "Selected cut at depth 13, code 83087, node 174677",
                "At remaining fuel 8 and original index 174677, selection on the full partial prefix of depth 13 and code 83087 returns the complete row with depth 13, base-four code 83087, original node 174677, kind 2, reserved field 0, 821 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-20747-173616", "unmarked_context_12_20747_173616", "Unmarked parent at depth 12, code 20747",
                "The frontier Boolean is false at remaining fuel 9, original node 173616, the whole prefixCache at depth 12 and code 20747, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-20770-174599", "unmarked_context_12_20770_174599", "Unmarked parent at depth 12, code 20770",
                "The frontier Boolean is false at remaining fuel 9, original node 174599, the whole prefixCache at depth 12 and code 20770, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-20747-173616", "node_context_12_20747_173616", "Original split at fuel 9 and node 173616",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 173533, 173588, 173608, 173615. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-20770-174599", "node_context_12_20770_174599", "Original split at fuel 9 and node 174599",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 174542, 174566, 174588, 174598. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-20747-173616", "context_12_20747_173616", "Context at depth 12, code 20747, node 173616",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 20747 and original node 173616, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_82988_173533, context_13_82989_173588, context_13_82990_173608, context_13_82991_173615.", DescribeRole.Theorem),
            Node("context-13-83087-174677", "context_13_83087_174677", "Context at depth 13, code 83087, node 174677",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 83087 and original node 174677, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
