using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0735Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0735.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0735",
        H("Original frontier context coverage 0735"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35283", "selected_cut_35283", "Selected cut at depth 12, code 285204, node 1738",
                "At remaining fuel 9 and original index 1738, selection on the full partial prefix of depth 12 and code 285204 returns the complete row with depth 12, base-four code 285204, original node 1738, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35330", "selected_cut_35330", "Selected cut at depth 11, code 71321, node 927453",
                "At remaining fuel 10 and original index 927453, selection on the full partial prefix of depth 11 and code 71321 returns the complete row with depth 11, base-four code 71321, original node 927453, kind 2, reserved field 0, 2477 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71300-925640", "unmarked_context_11_71300_925640", "Unmarked parent at depth 11, code 71300",
                "The frontier Boolean is false at remaining fuel 10, original node 925640, the whole prefixCache at depth 11 and code 71300, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-17828-927350", "unmarked_context_10_17828_927350", "Unmarked parent at depth 10, code 17828",
                "The frontier Boolean is false at remaining fuel 11, original node 927350, the whole prefixCache at depth 10 and code 17828, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71300-925640", "node_context_11_71300_925640", "Original split at fuel 10 and node 925640",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 925484, 925556, 925639. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-17828-927350", "node_context_10_17828_927350", "Original split at fuel 11 and node 927350",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 926969, 927094, 927195, 927349. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-71300-925640", "context_11_71300_925640", "Context at depth 11, code 71300, node 925640",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71300 and original node 925640, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_285200_1738, context_12_285201_925484, context_12_285202_925556, context_12_285203_925639.", DescribeRole.Theorem),
            Node("context-11-71321-927453", "context_11_71321_927453", "Context at depth 11, code 71321, node 927453",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71321 and original node 927453, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
