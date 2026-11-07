using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0387Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0387.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0387",
        H("Original frontier context coverage 0387"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18580", "selected_cut_18580", "Selected cut at depth 12, code 71740, node 475533",
                "At remaining fuel 9 and original index 475533, selection on the full partial prefix of depth 12 and code 71740 returns the complete row with depth 12, base-four code 71740, original node 475533, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18626", "selected_cut_18626", "Selected cut at depth 13, code 287054, node 476698",
                "At remaining fuel 8 and original index 476698, selection on the full partial prefix of depth 13 and code 287054 returns the complete row with depth 13, base-four code 287054, original node 476698, kind 2, reserved field 0, 1641 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71739-475531", "unmarked_context_12_71739_475531", "Unmarked parent at depth 12, code 71739",
                "The frontier Boolean is false at remaining fuel 9, original node 475531, the whole prefixCache at depth 12 and code 71739, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71762-476657", "unmarked_context_12_71762_476657", "Unmarked parent at depth 12, code 71762",
                "The frontier Boolean is false at remaining fuel 9, original node 476657, the whole prefixCache at depth 12 and code 71762, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71739-475531", "node_context_12_71739_475531", "Original split at fuel 9 and node 475531",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 475460, 475501, 475523, 475530. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71762-476657", "node_context_12_71762_476657", "Original split at fuel 9 and node 476657",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 476633, 476651, 476656. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-71739-475531", "context_12_71739_475531", "Context at depth 12, code 71739, node 475531",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71739 and original node 475531, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_286956_475460, context_13_286957_475501, context_13_286958_475523, context_13_286959_475530.", DescribeRole.Theorem),
            Node("context-13-287054-476698", "context_13_287054_476698", "Context at depth 13, code 287054, node 476698",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287054 and original node 476698, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
