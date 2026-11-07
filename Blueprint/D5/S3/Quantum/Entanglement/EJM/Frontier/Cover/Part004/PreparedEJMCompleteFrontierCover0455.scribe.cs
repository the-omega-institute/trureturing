using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0455Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0455.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0455",
        H("Original frontier context coverage 0455"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21844", "selected_cut_21844", "Selected cut at depth 13, code 301240, node 558329",
                "At remaining fuel 8 and original index 558329, selection on the full partial prefix of depth 13 and code 301240 returns the complete row with depth 13, base-four code 301240, original node 558329, kind 2, reserved field 0, 609 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21891", "selected_cut_21891", "Selected cut at depth 13, code 301290, node 559117",
                "At remaining fuel 8 and original index 559117, selection on the full partial prefix of depth 13 and code 301290 returns the complete row with depth 13, base-four code 301290, original node 559117, kind 2, reserved field 0, 2037 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75309-558318", "unmarked_context_12_75309_558318", "Unmarked parent at depth 12, code 75309",
                "The frontier Boolean is false at remaining fuel 9, original node 558318, the whole prefixCache at depth 12 and code 75309, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75321-559044", "unmarked_context_12_75321_559044", "Unmarked parent at depth 12, code 75321",
                "The frontier Boolean is false at remaining fuel 9, original node 559044, the whole prefixCache at depth 12 and code 75321, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75309-558318", "node_context_12_75309_558318", "Original split at fuel 9 and node 558318",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 558264, 558296, 558313, 558317. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75321-559044", "node_context_12_75321_559044", "Original split at fuel 9 and node 559044",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 558995, 559020, 559035, 559043. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75309-558318", "context_12_75309_558318", "Context at depth 12, code 75309, node 558318",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75309 and original node 558318, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_301236_558264, context_13_301237_558296, context_13_301238_558313, context_13_301239_558317.", DescribeRole.Theorem),
            Node("context-13-301290-559117", "context_13_301290_559117", "Context at depth 13, code 301290, node 559117",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 301290 and original node 559117, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
