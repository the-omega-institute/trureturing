using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0149Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0149.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0149",
        H("Original frontier context coverage 0149"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07155", "selected_cut_07155", "Selected cut at depth 13, code 88398, node 208788",
                "At remaining fuel 8 and original index 208788, selection on the full partial prefix of depth 13 and code 88398 returns the complete row with depth 13, base-four code 88398, original node 208788, kind 2, reserved field 0, 1681 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07202", "selected_cut_07202", "Selected cut at depth 13, code 88469, node 209762",
                "At remaining fuel 8 and original index 209762, selection on the full partial prefix of depth 13 and code 88469 returns the complete row with depth 13, base-four code 88469, original node 209762, kind 2, reserved field 0, 1529 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22099-208801", "unmarked_context_12_22099_208801", "Unmarked parent at depth 12, code 22099",
                "The frontier Boolean is false at remaining fuel 9, original node 208801, the whole prefixCache at depth 12 and code 22099, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5528-209696", "unmarked_context_11_5528_209696", "Unmarked parent at depth 11, code 5528",
                "The frontier Boolean is false at remaining fuel 10, original node 209696, the whole prefixCache at depth 11 and code 5528, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22099-208801", "node_context_12_22099_208801", "Original split at fuel 9 and node 208801",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 208768, 208788, 208800. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5528-209696", "node_context_11_5528_209696", "Original split at fuel 10 and node 209696",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 209530, 209606, 209648, 209695. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-88398-208788", "context_13_88398_208788", "Context at depth 13, code 88398, node 208788",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88398 and original node 208788, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-88469-209762", "context_13_88469_209762", "Context at depth 13, code 88469, node 209762",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88469 and original node 209762, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
