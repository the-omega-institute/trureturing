using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0081Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0081.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0081",
        H("Original frontier context coverage 0081"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03890", "selected_cut_03890", "Selected cut at depth 13, code 70760, node 124722",
                "At remaining fuel 8 and original index 124722, selection on the full partial prefix of depth 13 and code 70760 returns the complete row with depth 13, base-four code 70760, original node 124722, kind 2, reserved field 0, 1833 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03938", "selected_cut_03938", "Selected cut at depth 13, code 70823, node 125797",
                "At remaining fuel 8 and original index 125797, selection on the full partial prefix of depth 13 and code 70823 returns the complete row with depth 13, base-four code 70823, original node 125797, kind 2, reserved field 0, 769 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-17690-124781", "unmarked_context_12_17690_124781", "Unmarked parent at depth 12, code 17690",
                "The frontier Boolean is false at remaining fuel 9, original node 124781, the whole prefixCache at depth 12 and code 17690, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-17704-125721", "unmarked_context_12_17704_125721", "Unmarked parent at depth 12, code 17704",
                "The frontier Boolean is false at remaining fuel 9, original node 125721, the whole prefixCache at depth 12 and code 17704, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-17690-124781", "node_context_12_17690_124781", "Original split at fuel 9 and node 124781",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 124722, 124748, 124771, 124780. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-17704-125721", "node_context_12_17704_125721", "Original split at fuel 9 and node 125721",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 125665, 125685, 125710, 125720. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-70760-124722", "context_13_70760_124722", "Context at depth 13, code 70760, node 124722",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 70760 and original node 124722, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-70823-125797", "context_13_70823_125797", "Context at depth 13, code 70823, node 125797",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 70823 and original node 125797, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
