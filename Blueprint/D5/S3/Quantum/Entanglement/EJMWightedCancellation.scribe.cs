using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class EJMWightedCancellationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJMWightedCancellation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact weighted cancellation for transformed triangle inflation identities.",
        H("Weighted inflation cancellation"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-cancellation"),
                DeclarationHandle.Create(Prefix + "finite_weighted_block_cancellation"), H("Finite factor cancellation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary finite A and B, a block mass p(a)k(b) can be summed against any coefficient F by first contracting the A coordinate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("scaled-cancellation"),
                DeclarationHandle.Create(Prefix + "finite_scaled_weighted_block_cancellation"), H("Integer-scale cancellation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact denominator and score scales cancel the contracted target block. This is the algebraic consumer of the continuous inflation marginal identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bac-order"),
                DeclarationHandle.Create(Prefix + "triangle_mass_in_BAC_order"), H("Preserve B,A,C export order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A marginal map whose tuple is ordered B,A,C is interpreted using the actual party-labelled A,B,C arguments; no hidden-law symmetry is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-b"),
                DeclarationHandle.Create(Prefix + "singleton_mass_in_B_order"), H("B singleton marginal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The B singleton contributes the explicit sum over A and C outcomes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tuple-expectation"),
                DeclarationHandle.Create(Prefix + "inflation_expectation_tuple"), H("Actual tuple expectation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An injective tuple of observed nodes and its complement reindex the full finite law. Summing the complement yields the actual continuous-response marginal, so every tuple score has the same expectation under that marginal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("centered-expectation"),
                DeclarationHandle.Create(Prefix + "inflation_centered_expectation"), H("Independent centered block"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Disjoint actual source supports and a proven head marginal give zero expectation of the scaled head-and-tail score after exact target contraction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("centered-fin-expectation"),
                DeclarationHandle.Create(Prefix + "inflation_centered_fin_expectation"), H("Preserve finite export indexing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The consumed adapter preserves the original Fin(m+n) coefficient order when separating its first m outcomes from its remaining n outcomes."))), DescribeRole.Theorem))));
}
