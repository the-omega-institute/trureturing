using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0971Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0971.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0971",
        H("Original frontier context coverage 0971"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46612", "selected_cut_46612", "Selected cut at depth 10, code 23194, node 1300205",
                "At remaining fuel 11 and original index 1300205, selection on the full partial prefix of depth 10 and code 23194 returns the complete row with depth 10, base-four code 23194, original node 1300205, kind 2, reserved field 0, 2469 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46659", "selected_cut_46659", "Selected cut at depth 12, code 371238, node 1301830",
                "At remaining fuel 9 and original index 1301830, selection on the full partial prefix of depth 12 and code 371238 returns the complete row with depth 12, base-four code 371238, original node 1301830, kind 2, reserved field 0, 1833 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23193-1300156", "unmarked_context_10_23193_1300156", "Unmarked parent at depth 10, code 23193",
                "The frontier Boolean is false at remaining fuel 11, original node 1300156, the whole prefixCache at depth 10 and code 23193, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92808-1301795", "unmarked_context_11_92808_1301795", "Unmarked parent at depth 11, code 92808",
                "The frontier Boolean is false at remaining fuel 10, original node 1301795, the whole prefixCache at depth 11 and code 92808, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23193-1300156", "node_context_10_23193_1300156", "Original split at fuel 11 and node 1300156",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1300083, 1192826, 1300122, 1300155. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92808-1301795", "node_context_11_92808_1301795", "Original split at fuel 10 and node 1301795",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1301707, 1301743, 1301794. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23193-1300156", "context_10_23193_1300156", "Context at depth 10, code 23193, node 1300156",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23193 and original node 1300156, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_92772_1300083, context_11_92773_1192826, context_11_92774_1300122, context_11_92775_1300155.", DescribeRole.Theorem),
            Node("context-12-371238-1301830", "context_12_371238_1301830", "Context at depth 12, code 371238, node 1301830",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 371238 and original node 1301830, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
