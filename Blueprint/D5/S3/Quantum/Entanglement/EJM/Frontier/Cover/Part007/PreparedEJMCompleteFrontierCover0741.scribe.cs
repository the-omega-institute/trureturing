using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0741Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0741.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0741",
        H("Original frontier context coverage 0741"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35571", "selected_cut_35571", "Selected cut at depth 12, code 287004, node 935962",
                "At remaining fuel 9 and original index 935962, selection on the full partial prefix of depth 12 and code 287004 returns the complete row with depth 12, base-four code 287004, original node 935962, kind 2, reserved field 0, 3385 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35618", "selected_cut_35618", "Selected cut at depth 12, code 287054, node 937943",
                "At remaining fuel 9 and original index 937943, selection on the full partial prefix of depth 12 and code 287054 returns the complete row with depth 12, base-four code 287054, original node 937943, kind 2, reserved field 0, 1949 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71750-935905", "unmarked_context_11_71750_935905", "Unmarked parent at depth 11, code 71750",
                "The frontier Boolean is false at remaining fuel 10, original node 935905, the whole prefixCache at depth 11 and code 71750, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71762-937885", "unmarked_context_11_71762_937885", "Unmarked parent at depth 11, code 71762",
                "The frontier Boolean is false at remaining fuel 10, original node 937885, the whole prefixCache at depth 11 and code 71762, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71750-935905", "node_context_11_71750_935905", "Original split at fuel 10 and node 935905",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 935759, 935802, 935846, 935904. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71762-937885", "node_context_11_71762_937885", "Original split at fuel 10 and node 937885",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 937811, 896706, 937844, 937884. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-71750-935905", "context_11_71750_935905", "Context at depth 11, code 71750, node 935905",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71750 and original node 935905, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_287000_935759, context_12_287001_935802, context_12_287002_935846, context_12_287003_935904.", DescribeRole.Theorem),
            Node("context-12-287054-937943", "context_12_287054_937943", "Context at depth 12, code 287054, node 937943",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287054 and original node 937943, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
