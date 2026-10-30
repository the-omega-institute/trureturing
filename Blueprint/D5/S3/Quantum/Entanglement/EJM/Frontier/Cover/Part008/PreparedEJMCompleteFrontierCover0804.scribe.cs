using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0804Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0804.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0804",
        H("Original frontier context coverage 0804"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38596", "selected_cut_38596", "Selected cut at depth 12, code 301690, node 893903",
                "At remaining fuel 9 and original index 893903, selection on the full partial prefix of depth 12 and code 301690 returns the complete row with depth 12, base-four code 301690, original node 893903, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38642", "selected_cut_38642", "Selected cut at depth 12, code 301832, node 1043446",
                "At remaining fuel 9 and original index 1043446, selection on the full partial prefix of depth 12 and code 301832 returns the complete row with depth 12, base-four code 301832, original node 1043446, kind 2, reserved field 0, 3693 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75422-1041729", "unmarked_context_11_75422_1041729", "Unmarked parent at depth 11, code 75422",
                "The frontier Boolean is false at remaining fuel 10, original node 1041729, the whole prefixCache at depth 11 and code 75422, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75457-1043384", "unmarked_context_11_75457_1043384", "Unmarked parent at depth 11, code 75457",
                "The frontier Boolean is false at remaining fuel 10, original node 1043384, the whole prefixCache at depth 11 and code 75457, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75422-1041729", "node_context_11_75422_1041729", "Original split at fuel 10 and node 1041729",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1041660, 1041696, 893903, 1041728. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75457-1043384", "node_context_11_75457_1043384", "Original split at fuel 10 and node 1043384",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1043174, 1043249, 1043326, 1043383. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-301690-893903", "context_12_301690_893903", "Context at depth 12, code 301690, node 893903",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301690 and original node 893903, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-301832-1043446", "context_12_301832_1043446", "Context at depth 12, code 301832, node 1043446",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301832 and original node 1043446, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
