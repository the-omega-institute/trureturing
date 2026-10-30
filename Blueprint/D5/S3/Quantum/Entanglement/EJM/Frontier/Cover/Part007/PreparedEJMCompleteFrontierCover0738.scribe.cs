using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0738Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0738.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0738",
        H("Original frontier context coverage 0738"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35427", "selected_cut_35427", "Selected cut at depth 12, code 285573, node 931099",
                "At remaining fuel 9 and original index 931099, selection on the full partial prefix of depth 12 and code 285573 returns the complete row with depth 12, base-four code 285573, original node 931099, kind 2, reserved field 0, 1149 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35473", "selected_cut_35473", "Selected cut at depth 12, code 286747, node 932627",
                "At remaining fuel 9 and original index 932627, selection on the full partial prefix of depth 12 and code 286747 returns the complete row with depth 12, base-four code 286747, original node 932627, kind 2, reserved field 0, 2833 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71393-931128", "unmarked_context_11_71393_931128", "Unmarked parent at depth 11, code 71393",
                "The frontier Boolean is false at remaining fuel 10, original node 931128, the whole prefixCache at depth 11 and code 71393, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71686-932628", "unmarked_context_11_71686_932628", "Unmarked parent at depth 11, code 71686",
                "The frontier Boolean is false at remaining fuel 10, original node 932628, the whole prefixCache at depth 11 and code 71686, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71393-931128", "node_context_11_71393_931128", "Original split at fuel 10 and node 931128",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 931082, 931099, 931114, 931127. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71686-932628", "node_context_11_71686_932628", "Original split at fuel 10 and node 932628",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 932548, 932582, 932627. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-285573-931099", "context_12_285573_931099", "Context at depth 12, code 285573, node 931099",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 285573 and original node 931099, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-71686-932628", "context_11_71686_932628", "Context at depth 11, code 71686, node 932628",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71686 and original node 932628, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_286744_1738, context_12_286745_932548, context_12_286746_932582, context_12_286747_932627.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
