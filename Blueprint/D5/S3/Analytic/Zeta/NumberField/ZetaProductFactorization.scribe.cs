using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.NumberField;

internal sealed class ZetaProductFactorizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zeta Product Factorization.",
        H("Zeta Product Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("artin-dirichlet-series"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization.artinDirichletSeries"),
                H("artin Dirichlet Series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The Dirichlet series L_χ(s) = ∑'_{𝔞 ≠ ⊥} χ(𝔞) N𝔞^{-s} of a Galois character, as a " +
                    "function of s. This is the analytic engine of Sharifi 7.1.16–7.1.19; for 1 < Re s it " +
                    "equals the Euler product over unramified primes " +
                    "(exists_artinLSeries_eulerProduct_abelian)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("log-norm-ramified-factor-bounded"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization.log_norm_ramified_factor_bounded"),
                H("Zeta Product Factorization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For the Euler product R(s) over prime ideals of L lying above primes ramified in " +
                    "L/K, there is a real C such that |log ‖R(s)‖| ≤ C eventually as real s decreases " +
                    "to one from above. This is the bounded logarithmic ramification correction in the " +
                    "factorisation argument."))),
                DescribeRole.Theorem)
        )));
}
