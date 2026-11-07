using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0651Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0651.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0651",
        H("Original frontier context coverage 0651"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31252", "selected_cut_31252", "Selected cut at depth 13, code 423007, node 798804",
                "At remaining fuel 8 and original index 798804, selection on the full partial prefix of depth 13 and code 423007 returns the complete row with depth 13, base-four code 423007, original node 798804, kind 2, reserved field 0, 1049 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31298", "selected_cut_31298", "Selected cut at depth 12, code 105764, node 461082",
                "At remaining fuel 9 and original index 461082, selection on the full partial prefix of depth 12 and code 105764 returns the complete row with depth 12, base-four code 105764, original node 461082, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-105751-798805", "unmarked_context_12_105751_798805", "Unmarked parent at depth 12, code 105751",
                "The frontier Boolean is false at remaining fuel 9, original node 798805, the whole prefixCache at depth 12 and code 105751, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-26440-800749", "unmarked_context_11_26440_800749", "Unmarked parent at depth 11, code 26440",
                "The frontier Boolean is false at remaining fuel 10, original node 800749, the whole prefixCache at depth 11 and code 26440, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-105751-798805", "node_context_12_105751_798805", "Original split at fuel 9 and node 798805",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 798643, 798700, 798785, 798804. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-26440-800749", "node_context_11_26440_800749", "Original split at fuel 10 and node 800749",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 800368, 772506, 800524, 800748. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-423007-798804", "context_13_423007_798804", "Context at depth 13, code 423007, node 798804",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 423007 and original node 798804, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-105764-461082", "context_12_105764_461082", "Context at depth 12, code 105764, node 461082",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105764 and original node 461082, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
