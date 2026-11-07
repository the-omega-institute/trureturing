using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0422Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0422.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0422",
        H("Original frontier context coverage 0422"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20258", "selected_cut_20258", "Selected cut at depth 13, code 295001, node 518596",
                "At remaining fuel 8 and original index 518596, selection on the full partial prefix of depth 13 and code 295001 returns the complete row with depth 13, base-four code 295001, original node 518596, kind 2, reserved field 0, 1721 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20305", "selected_cut_20305", "Selected cut at depth 12, code 73771, node 520091",
                "At remaining fuel 9 and original index 520091, selection on the full partial prefix of depth 12 and code 73771 returns the complete row with depth 12, base-four code 73771, original node 520091, kind 2, reserved field 0, 3653 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-73750-518622", "unmarked_context_12_73750_518622", "Unmarked parent at depth 12, code 73750",
                "The frontier Boolean is false at remaining fuel 9, original node 518622, the whole prefixCache at depth 12 and code 73750, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18442-520092", "unmarked_context_11_18442_520092", "Unmarked parent at depth 11, code 18442",
                "The frontier Boolean is false at remaining fuel 10, original node 520092, the whole prefixCache at depth 11 and code 18442, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-73750-518622", "node_context_12_73750_518622", "Original split at fuel 9 and node 518622",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 518572, 518596, 518616, 518621. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18442-520092", "node_context_11_18442_520092", "Original split at fuel 10 and node 520092",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 519951, 520023, 520091. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-295001-518596", "context_13_295001_518596", "Context at depth 13, code 295001, node 518596",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 295001 and original node 518596, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-18442-520092", "context_11_18442_520092", "Context at depth 11, code 18442, node 520092",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18442 and original node 520092, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_73768_435790, context_12_73769_519951, context_12_73770_520023, context_12_73771_520091.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
