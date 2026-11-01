using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0285Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0285.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0285",
        H("Original frontier context coverage 0285"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13683", "selected_cut_13683", "Selected cut at depth 13, code 107559, node 358501",
                "At remaining fuel 8 and original index 358501, selection on the full partial prefix of depth 13 and code 107559 returns the complete row with depth 13, base-four code 107559, original node 358501, kind 2, reserved field 0, 1173 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13729", "selected_cut_13729", "Selected cut at depth 13, code 107599, node 359703",
                "At remaining fuel 8 and original index 359703, selection on the full partial prefix of depth 13 and code 107599 returns the complete row with depth 13, base-four code 107599, original node 359703, kind 2, reserved field 0, 1013 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26889-358502", "unmarked_context_12_26889_358502", "Unmarked parent at depth 12, code 26889",
                "The frontier Boolean is false at remaining fuel 9, original node 358502, the whole prefixCache at depth 12 and code 26889, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6724-359705", "unmarked_context_11_6724_359705", "Unmarked parent at depth 11, code 6724",
                "The frontier Boolean is false at remaining fuel 10, original node 359705, the whole prefixCache at depth 11 and code 6724, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26889-358502", "node_context_12_26889_358502", "Original split at fuel 9 and node 358502",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 358438, 358471, 358494, 358501. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6724-359705", "node_context_11_6724_359705", "Original split at fuel 10 and node 359705",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 359486, 359547, 359624, 359704. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-107559-358501", "context_13_107559_358501", "Context at depth 13, code 107559, node 358501",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 107559 and original node 358501, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-6724-359705", "context_11_6724_359705", "Context at depth 11, code 6724, node 359705",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6724 and original node 359705, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_26896_359486, context_12_26897_359547, context_12_26898_359624, context_12_26899_359704.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
