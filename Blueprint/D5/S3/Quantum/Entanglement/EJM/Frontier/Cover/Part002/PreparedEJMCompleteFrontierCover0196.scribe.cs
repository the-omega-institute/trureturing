using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0196Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0196.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0196",
        H("Original frontier context coverage 0196"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09411", "selected_cut_09411", "Selected cut at depth 13, code 93513, node 259804",
                "At remaining fuel 8 and original index 259804, selection on the full partial prefix of depth 13 and code 93513 returns the complete row with depth 13, base-four code 93513, original node 259804, kind 2, reserved field 0, 2769 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09459", "selected_cut_09459", "Selected cut at depth 13, code 93567, node 260808",
                "At remaining fuel 8 and original index 260808, selection on the full partial prefix of depth 13 and code 93567 returns the complete row with depth 13, base-four code 93567, original node 260808, kind 2, reserved field 0, 1205 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23378-259857", "unmarked_context_12_23378_259857", "Unmarked parent at depth 12, code 23378",
                "The frontier Boolean is false at remaining fuel 9, original node 259857, the whole prefixCache at depth 12 and code 23378, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23391-260809", "unmarked_context_12_23391_260809", "Unmarked parent at depth 12, code 23391",
                "The frontier Boolean is false at remaining fuel 9, original node 260809, the whole prefixCache at depth 12 and code 23391, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23378-259857", "node_context_12_23378_259857", "Original split at fuel 9 and node 259857",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 259804, 259842, 259856. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23391-260809", "node_context_12_23391_260809", "Original split at fuel 9 and node 260809",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 260715, 260777, 260808. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-93513-259804", "context_13_93513_259804", "Context at depth 13, code 93513, node 259804",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93513 and original node 259804, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-23391-260809", "context_12_23391_260809", "Context at depth 12, code 23391, node 260809",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23391 and original node 260809, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_93564_3444, context_13_93565_260715, context_13_93566_260777, context_13_93567_260808.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
