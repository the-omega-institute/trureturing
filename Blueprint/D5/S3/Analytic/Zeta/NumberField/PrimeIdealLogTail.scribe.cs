using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.NumberFieldZeta;

internal sealed class PrimeIdealLogTailDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime Ideal Log Tail.",
        H("Prime Ideal Log Tail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-ideal-zeta-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.primeIdealZetaSum"),
                H("prime Ideal Zeta Sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Partial Dirichlet series Σ_{𝔭 ∈ S} N𝔭^{-s} over nonzero prime ideals 𝔭 of 𝓞 K lying " +
                    "in the set S."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("has-dirichlet-density"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.HasDirichletDensity"),
                H("Has Dirichlet Density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The Dirichlet density of a set S of prime ideals of 𝓞 K is δ when the ratio of " +
                    "partial sums tends to δ as s ↓ 1. Sharifi 7.1.13: δ(S) = lim_{s → 1⁺} (Σ_{𝔭 ∈ S} " +
                    "N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("has-lower-dirichlet-density"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.HasLowerDirichletDensity"),
                H("Has Lower Dirichlet Density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Lower Dirichlet density (liminf of the ratio), matching Sharifi's δ_inf notation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("abs-tsum-neg-log-one-sub-sub-rpow-le"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.abs_tsum_neg_log_one_sub_sub_rpow_le"),
                H("Prime Ideal Log Tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The remainder Σ_𝔭 (-log(1 - N𝔭^{-s}) - N𝔭^{-s}) is bounded near s = 1 (Sharifi " +
                    "7.1.12)."))),
                DescribeRole.Theorem)
        )));
}
