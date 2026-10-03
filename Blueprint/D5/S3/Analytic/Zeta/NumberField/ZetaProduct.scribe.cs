using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.NumberFieldZeta;

internal sealed class ZetaProductDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zeta Product.",
        H("Zeta Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("artin-l-series-one-ne-zero"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProduct.artinLSeries_one_ne_zero"),
                H("Zeta Product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite abelian cyclotomic Galois extension L/K of modulus m with m ≥ 1 " +
                    "and m % 4 ≠ 2, let χ be a nontrivial Galois character. Every function F analytic " +
                    "on Re(s) > 1 - 1/[K:ℚ] that agrees on Re(s) > 1 with the χ-weighted " +
                    "nonzero-ideal Dirichlet series satisfies F(1) ≠ 0."))),
                DescribeRole.Theorem)
        )));
}
