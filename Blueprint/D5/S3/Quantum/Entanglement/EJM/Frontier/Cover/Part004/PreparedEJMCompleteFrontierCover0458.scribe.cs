using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0458Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0458.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0458",
        H("Original frontier context coverage 0458"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21988", "selected_cut_21988", "Selected cut at depth 13, code 301420, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 301420 returns the complete row with depth 13, base-four code 301420, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22034", "selected_cut_22034", "Selected cut at depth 12, code 75380, node 561889",
                "At remaining fuel 9 and original index 561889, selection on the full partial prefix of depth 12 and code 75380 returns the complete row with depth 12, base-four code 75380, original node 561889, kind 2, reserved field 0, 2749 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75354-560797", "unmarked_context_12_75354_560797", "Unmarked parent at depth 12, code 75354",
                "The frontier Boolean is false at remaining fuel 9, original node 560797, the whole prefixCache at depth 12 and code 75354, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18844-561855", "unmarked_context_11_18844_561855", "Unmarked parent at depth 11, code 18844",
                "The frontier Boolean is false at remaining fuel 10, original node 561855, the whole prefixCache at depth 11 and code 18844, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75354-560797", "node_context_12_75354_560797", "Original split at fuel 9 and node 560797",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 560697, 560757, 560796. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18844-561855", "node_context_11_18844_561855", "Original split at fuel 10 and node 561855",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 561743, 561778, 561817, 561854. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75354-560797", "context_12_75354_560797", "Context at depth 12, code 75354, node 560797",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75354 and original node 560797, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_301416_3444, context_13_301417_560697, context_13_301418_560757, context_13_301419_560796.", DescribeRole.Theorem),
            Node("context-12-75380-561889", "context_12_75380_561889", "Context at depth 12, code 75380, node 561889",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75380 and original node 561889, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
