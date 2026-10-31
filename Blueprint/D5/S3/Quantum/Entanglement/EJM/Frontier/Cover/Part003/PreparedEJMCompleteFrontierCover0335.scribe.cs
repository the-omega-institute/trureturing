using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0335Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0335.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0335",
        H("Original frontier context coverage 0335"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16084", "selected_cut_16084", "Selected cut at depth 12, code 28063, node 409850",
                "At remaining fuel 9 and original index 409850, selection on the full partial prefix of depth 12 and code 28063 returns the complete row with depth 12, base-four code 28063, original node 409850, kind 2, reserved field 0, 2093 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16130", "selected_cut_16130", "Selected cut at depth 13, code 112649, node 410903",
                "At remaining fuel 8 and original index 410903, selection on the full partial prefix of depth 13 and code 112649 returns the complete row with depth 13, base-four code 112649, original node 410903, kind 2, reserved field 0, 1753 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-7015-409851", "unmarked_context_11_7015_409851", "Unmarked parent at depth 11, code 7015",
                "The frontier Boolean is false at remaining fuel 10, original node 409851, the whole prefixCache at depth 11 and code 7015, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-109-410768", "unmarked_context_8_109_410768", "Unmarked parent at depth 8, code 109",
                "The frontier Boolean is false at remaining fuel 13, original node 410768, the whole prefixCache at depth 8 and code 109, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-7015-409851", "node_context_11_7015_409851", "Original split at fuel 10 and node 409851",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 409786, 409803, 409831, 409850. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-109-410768", "node_context_8_109_410768", "Original split at fuel 13 and node 410768",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 405548, 408933, 410459, 410767. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-28063-409850", "context_12_28063_409850", "Context at depth 12, code 28063, node 409850",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28063 and original node 409850, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-112649-410903", "context_13_112649_410903", "Context at depth 13, code 112649, node 410903",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112649 and original node 410903, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
