using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0533Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0533.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0533",
        H("Original frontier context coverage 0533"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25588", "selected_cut_25588", "Selected cut at depth 12, code 87664, node 648078",
                "At remaining fuel 9 and original index 648078, selection on the full partial prefix of depth 12 and code 87664 returns the complete row with depth 12, base-four code 87664, original node 648078, kind 2, reserved field 0, 1365 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25634", "selected_cut_25634", "Selected cut at depth 13, code 352298, node 649478",
                "At remaining fuel 8 and original index 649478, selection on the full partial prefix of depth 13 and code 352298 returns the complete row with depth 13, base-four code 352298, original node 649478, kind 2, reserved field 0, 701 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-21915-648054", "unmarked_context_11_21915_648054", "Unmarked parent at depth 11, code 21915",
                "The frontier Boolean is false at remaining fuel 10, original node 648054, the whole prefixCache at depth 11 and code 21915, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-88073-649325", "unmarked_context_12_88073_649325", "Unmarked parent at depth 12, code 88073",
                "The frontier Boolean is false at remaining fuel 9, original node 649325, the whole prefixCache at depth 12 and code 88073, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-21915-648054", "node_context_11_21915_648054", "Original split at fuel 10 and node 648054",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 647964, 648009, 648033, 648053. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-88073-649325", "node_context_12_88073_649325", "Original split at fuel 9 and node 649325",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 649236, 649284, 649315, 649324. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-21915-648054", "context_11_21915_648054", "Context at depth 11, code 21915, node 648054",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 21915 and original node 648054, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_87660_647964, context_12_87661_648009, context_12_87662_648033, context_12_87663_648053.", DescribeRole.Theorem),
            Node("context-13-352298-649478", "context_13_352298_649478", "Context at depth 13, code 352298, node 649478",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 352298 and original node 649478, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
