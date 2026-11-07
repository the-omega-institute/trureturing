using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0776Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0776.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0776",
        H("Original frontier context coverage 0776"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37251", "selected_cut_37251", "Selected cut at depth 13, code 1198176, node 995098",
                "At remaining fuel 8 and original index 995098, selection on the full partial prefix of depth 13 and code 1198176 returns the complete row with depth 13, base-four code 1198176, original node 995098, kind 2, reserved field 0, 1497 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37298", "selected_cut_37298", "Selected cut at depth 12, code 299573, node 996576",
                "At remaining fuel 9 and original index 996576, selection on the full partial prefix of depth 12 and code 299573 returns the complete row with depth 12, base-four code 299573, original node 996576, kind 2, reserved field 0, 3805 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-74885-995076", "unmarked_context_11_74885_995076", "Unmarked parent at depth 11, code 74885",
                "The frontier Boolean is false at remaining fuel 10, original node 995076, the whole prefixCache at depth 11 and code 74885, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-74892-996434", "unmarked_context_11_74892_996434", "Unmarked parent at depth 11, code 74892",
                "The frontier Boolean is false at remaining fuel 10, original node 996434, the whole prefixCache at depth 11 and code 74892, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-74885-995076", "node_context_11_74885_995076", "Original split at fuel 10 and node 995076",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994808, 994956, 995010, 995075. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-74892-996434", "node_context_11_74892_996434", "Original split at fuel 10 and node 996434",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994572, 996353, 996392, 996433. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-74885-995076", "context_11_74885_995076", "Context at depth 11, code 74885, node 995076",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 74885 and original node 995076, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_299540_994808, context_12_299541_994956, context_12_299542_995010, context_12_299543_995075.", DescribeRole.Theorem),
            Node("context-12-299573-996576", "context_12_299573_996576", "Context at depth 12, code 299573, node 996576",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299573 and original node 996576, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
