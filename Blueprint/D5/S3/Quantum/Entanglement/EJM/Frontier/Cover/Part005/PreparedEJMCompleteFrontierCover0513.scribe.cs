using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0513Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0513.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0513",
        H("Original frontier context coverage 0513"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24628", "selected_cut_24628", "Selected cut at depth 13, code 309340, node 622550",
                "At remaining fuel 8 and original index 622550, selection on the full partial prefix of depth 13 and code 309340 returns the complete row with depth 13, base-four code 309340, original node 622550, kind 2, reserved field 0, 1849 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24674", "selected_cut_24674", "Selected cut at depth 12, code 77348, node 450498",
                "At remaining fuel 9 and original index 450498, selection on the full partial prefix of depth 12 and code 77348 returns the complete row with depth 12, base-four code 77348, original node 450498, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77334-622509", "unmarked_context_12_77334_622509", "Unmarked parent at depth 12, code 77334",
                "The frontier Boolean is false at remaining fuel 9, original node 622509, the whole prefixCache at depth 12 and code 77334, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19336-623751", "unmarked_context_11_19336_623751", "Unmarked parent at depth 11, code 19336",
                "The frontier Boolean is false at remaining fuel 10, original node 623751, the whole prefixCache at depth 11 and code 19336, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77334-622509", "node_context_12_77334_622509", "Original split at fuel 9 and node 622509",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 622439, 622478, 622498, 622508. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19336-623751", "node_context_11_19336_623751", "Original split at fuel 10 and node 623751",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 623591, 623662, 623750. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-77334-622509", "context_12_77334_622509", "Context at depth 12, code 77334, node 622509",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77334 and original node 622509, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_309336_622439, context_13_309337_622478, context_13_309338_622498, context_13_309339_622508.", DescribeRole.Theorem),
            Node("context-12-77348-450498", "context_12_77348_450498", "Context at depth 12, code 77348, node 450498",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77348 and original node 450498, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
