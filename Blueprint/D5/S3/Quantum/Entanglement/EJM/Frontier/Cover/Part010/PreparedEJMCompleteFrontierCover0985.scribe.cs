using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0985Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0985.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0985",
        H("Original frontier context coverage 0985"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47283", "selected_cut_47283", "Selected cut at depth 11, code 93213, node 1322989",
                "At remaining fuel 10 and original index 1322989, selection on the full partial prefix of depth 11 and code 93213 returns the complete row with depth 11, base-four code 93213, original node 1322989, kind 2, reserved field 0, 3953 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47330", "selected_cut_47330", "Selected cut at depth 12, code 373025, node 1324304",
                "At remaining fuel 9 and original index 1324304, selection on the full partial prefix of depth 12 and code 373025 returns the complete row with depth 12, base-four code 373025, original node 1324304, kind 2, reserved field 0, 2337 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93214-1323073", "unmarked_context_11_93214_1323073", "Unmarked parent at depth 11, code 93214",
                "The frontier Boolean is false at remaining fuel 10, original node 1323073, the whole prefixCache at depth 11 and code 93214, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23313-1324264", "unmarked_context_10_23313_1324264", "Unmarked parent at depth 10, code 23313",
                "The frontier Boolean is false at remaining fuel 11, original node 1324264, the whole prefixCache at depth 10 and code 23313, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93214-1323073", "node_context_11_93214_1323073", "Original split at fuel 10 and node 1323073",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1323012, 1323033, 1323051, 1323072. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23313-1324264", "node_context_10_23313_1324264", "Original split at fuel 11 and node 1324264",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1324057, 815620, 1324134, 1324263. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-93213-1322989", "context_11_93213_1322989", "Context at depth 11, code 93213, node 1322989",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93213 and original node 1322989, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-373025-1324304", "context_12_373025_1324304", "Context at depth 12, code 373025, node 1324304",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 373025 and original node 1324304, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
