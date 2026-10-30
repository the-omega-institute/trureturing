using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0378Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0378.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0378",
        H("Original frontier context coverage 0378"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18146", "selected_cut_18146", "Selected cut at depth 12, code 71216, node 445562",
                "At remaining fuel 9 and original index 445562, selection on the full partial prefix of depth 12 and code 71216 returns the complete row with depth 12, base-four code 71216, original node 445562, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18195", "selected_cut_18195", "Selected cut at depth 13, code 284919, node 466192",
                "At remaining fuel 8 and original index 466192, selection on the full partial prefix of depth 13 and code 284919 returns the complete row with depth 13, base-four code 284919, original node 466192, kind 2, reserved field 0, 733 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71217-465262", "unmarked_context_12_71217_465262", "Unmarked parent at depth 12, code 71217",
                "The frontier Boolean is false at remaining fuel 9, original node 465262, the whole prefixCache at depth 12 and code 71217, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71228-466137", "unmarked_context_12_71228_466137", "Unmarked parent at depth 12, code 71228",
                "The frontier Boolean is false at remaining fuel 9, original node 466137, the whole prefixCache at depth 12 and code 71228, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71217-465262", "node_context_12_71217_465262", "Original split at fuel 9 and node 465262",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 465208, 465237, 465253, 465261. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71228-466137", "node_context_12_71228_466137", "Original split at fuel 9 and node 466137",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 466048, 466108, 466130, 466136. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-71216-445562", "context_12_71216_445562", "Context at depth 12, code 71216, node 445562",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71216 and original node 445562, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-284919-466192", "context_13_284919_466192", "Context at depth 13, code 284919, node 466192",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 284919 and original node 466192, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
