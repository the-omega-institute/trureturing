using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0460Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0460.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0460",
        H("Original frontier context coverage 0460"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22083", "selected_cut_22083", "Selected cut at depth 12, code 75426, node 563023",
                "At remaining fuel 9 and original index 563023, selection on the full partial prefix of depth 12 and code 75426 returns the complete row with depth 12, base-four code 75426, original node 563023, kind 2, reserved field 0, 1381 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22130", "selected_cut_22130", "Selected cut at depth 13, code 302108, node 563986",
                "At remaining fuel 8 and original index 563986, selection on the full partial prefix of depth 13 and code 302108 returns the complete row with depth 13, base-four code 302108, original node 563986, kind 2, reserved field 0, 2745 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18856-563038", "unmarked_context_11_18856_563038", "Unmarked parent at depth 11, code 18856",
                "The frontier Boolean is false at remaining fuel 10, original node 563038, the whole prefixCache at depth 11 and code 18856, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75526-563927", "unmarked_context_12_75526_563927", "Unmarked parent at depth 12, code 75526",
                "The frontier Boolean is false at remaining fuel 9, original node 563927, the whole prefixCache at depth 12 and code 75526, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18856-563038", "node_context_11_18856_563038", "Original split at fuel 10 and node 563038",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 562998, 563011, 563023, 563037. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75526-563927", "node_context_12_75526_563927", "Original split at fuel 9 and node 563927",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 563835, 563890, 563918, 563926. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75426-563023", "context_12_75426_563023", "Context at depth 12, code 75426, node 563023",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75426 and original node 563023, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-302108-563986", "context_13_302108_563986", "Context at depth 13, code 302108, node 563986",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302108 and original node 563986, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
