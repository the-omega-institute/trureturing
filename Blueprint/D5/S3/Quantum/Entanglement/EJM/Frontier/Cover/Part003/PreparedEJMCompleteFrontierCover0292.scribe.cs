using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0292Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0292.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0292",
        H("Original frontier context coverage 0292"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14020", "selected_cut_14020", "Selected cut at depth 12, code 26980, node 364290",
                "At remaining fuel 9 and original index 364290, selection on the full partial prefix of depth 12 and code 26980 returns the complete row with depth 12, base-four code 26980, original node 364290, kind 2, reserved field 0, 3465 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14067", "selected_cut_14067", "Selected cut at depth 12, code 27003, node 365236",
                "At remaining fuel 9 and original index 365236, selection on the full partial prefix of depth 12 and code 27003 returns the complete row with depth 12, base-four code 27003, original node 365236, kind 2, reserved field 0, 3789 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26979-364256", "unmarked_context_12_26979_364256", "Unmarked parent at depth 12, code 26979",
                "The frontier Boolean is false at remaining fuel 9, original node 364256, the whole prefixCache at depth 12 and code 26979, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27001-365163", "unmarked_context_12_27001_365163", "Unmarked parent at depth 12, code 27001",
                "The frontier Boolean is false at remaining fuel 9, original node 365163, the whole prefixCache at depth 12 and code 27001, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26979-364256", "node_context_12_26979_364256", "Original split at fuel 9 and node 364256",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 364224, 364247, 364255. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27001-365163", "node_context_12_27001_365163", "Original split at fuel 9 and node 365163",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 365120, 365143, 365162. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26979-364256", "context_12_26979_364256", "Context at depth 12, code 26979, node 364256",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26979 and original node 364256, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_107916_3444, context_13_107917_364224, context_13_107918_364247, context_13_107919_364255.", DescribeRole.Theorem),
            Node("context-12-27003-365236", "context_12_27003_365236", "Context at depth 12, code 27003, node 365236",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27003 and original node 365236, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
