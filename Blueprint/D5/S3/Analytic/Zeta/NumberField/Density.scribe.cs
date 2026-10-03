using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.NumberField;

internal sealed class DensityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Density of a finite set of primes is 0.",
        H("Density of a finite set of primes is 0"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("has-dirichlet-density-of-finite"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/Density.hasDirichletDensity_of_finite"),
                H("Density of a finite set of primes is 0"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Density of a finite set of primes is 0 (Sharifi 7.1.13). The numerator Σ_{𝔭 ∈ S} " +
                    "N𝔭^{-s} is bounded (finitely many terms, each ≤ 1) while the denominator Σ_𝔭 N𝔭^{-s} " +
                    "→ ∞, so the ratio → 0."))),
                DescribeRole.Theorem)
        )));
}
