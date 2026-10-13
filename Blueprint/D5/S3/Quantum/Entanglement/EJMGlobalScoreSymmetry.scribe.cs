using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class EJMGlobalScoreSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJMGlobalScoreSymmetry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual EJM score invariance and context-specific lexicographic symmetry cuts.",
        H("The original source and outcome actions earn every global cut"),
        Blocks(
            Paragraph(Text("The 192 exact source-copy maps and their block transports are reused from the score-symmetry module. The same 24 outcome maps are reused from the local producer; a source-major tag decodes the combined action. Nodes already are Fin 20, so no new node-order conversion or duplicate symmetry table is introduced.")),
            Describe.Lean(DescribeId.Create("score-invariant"),
                DeclarationHandle.Create(Prefix + "actual_score_invariant"),
                H("Every actual combined action preserves the complete centered score"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact global action composes the checked source-copy permutation with a common checked outcome permutation. Existing coefficient and centered-block invariance give equality of the complete 32-block integer score under this actual action."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-descent"),
                DeclarationHandle.Create(Prefix + "dominates_rank_lt"),
                H("A checked partial cut strictly decreases every actual completion's rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cut checks a strict decrease at its stored actual pivot and equality of every earlier transformed coordinate. Unknown values are accepted only when both the source coordinate and every outcome value are fixed. The generic finite lexicographic descent theorem then lowers the rank of every compatible full event. A shared branch shape must evaluate this predicate in each actual reached partial context; these symmetry facts do not transfer arithmetic bound receipts between different contexts."))), DescribeRole.Theorem))));
}
