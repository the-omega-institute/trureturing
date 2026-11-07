using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0539Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0539.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0539",
        H("Original frontier context coverage 0539"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25875", "selected_cut_25875", "Selected cut at depth 13, code 352611, node 655029",
                "At remaining fuel 8 and original index 655029, selection on the full partial prefix of depth 13 and code 352611 returns the complete row with depth 13, base-four code 352611, original node 655029, kind 2, reserved field 0, 1001 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25922", "selected_cut_25922", "Selected cut at depth 12, code 88175, node 655970",
                "At remaining fuel 9 and original index 655970, selection on the full partial prefix of depth 12 and code 88175 returns the complete row with depth 12, base-four code 88175, original node 655970, kind 2, reserved field 0, 2769 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88152-655030", "unmarked_context_12_88152_655030", "Unmarked parent at depth 12, code 88152",
                "The frontier Boolean is false at remaining fuel 9, original node 655030, the whole prefixCache at depth 12 and code 88152, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22043-655971", "unmarked_context_11_22043_655971", "Unmarked parent at depth 11, code 22043",
                "The frontier Boolean is false at remaining fuel 10, original node 655971, the whole prefixCache at depth 11 and code 22043, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88152-655030", "node_context_12_88152_655030", "Original split at fuel 9 and node 655030",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 655005, 655024, 655029. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22043-655971", "node_context_11_22043_655971", "Original split at fuel 10 and node 655971",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 655847, 655900, 655935, 655970. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-352611-655029", "context_13_352611_655029", "Context at depth 13, code 352611, node 655029",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 352611 and original node 655029, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-22043-655971", "context_11_22043_655971", "Context at depth 11, code 22043, node 655971",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 22043 and original node 655971, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_88172_655847, context_12_88173_655900, context_12_88174_655935, context_12_88175_655970.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
