using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class CyclotomicCharacterBoundsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic input of the cyclotomic case (Dirichlet's argument).",
        H("Analytic input of the cyclotomic case (Dirichlet's argument)"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("twisted-prime-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/CyclotomicCharacterBounds.twistedPrimeSum"),
                H("twisted Prime Sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The twisted prime sum ∑'_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ over the unramified primes, as a complex " +
                    "function of s. The χ = 1 value is the real prime sum ∑'_𝔭 N𝔭⁻ˢ; the χ ≠ 1 values are " +
                    "bounded near s = 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("artin-l-series-prime-sum-bounded-of-ne-one"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/CyclotomicCharacterBounds.artinLSeries_prime_sum_bounded_of_ne_one"),
                H("Analytic input of the cyclotomic case (Dirichlet's argument)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite abelian cyclotomic Galois extension L/K of modulus m with m ≥ 1 " +
                    "and m % 4 ≠ 2, and a nontrivial Galois character χ, the twisted sum over " +
                    "unramified prime ideals Σ_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ stays bounded as s ↓ 1. " +
                    "Now discharged modulo the complex-analytic bridge: produce the analytic extension Lf " +
                    "(LF4 artinLSeries_analytic_extension, itself ⟸ the geometry-of-numbers leaf " +
                    "character_sum_geometry_of_numbers_bound), note Lf 1 ≠ 0 (LF5 " +
                    "artinLSeries_one_ne_zero), and feed both to " +
                    "artinLSeries_prime_sum_bounded_of_analytic_extension."))),
                DescribeRole.Theorem)
        )));
}
