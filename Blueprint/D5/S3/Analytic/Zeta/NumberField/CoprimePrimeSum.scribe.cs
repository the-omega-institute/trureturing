using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.NumberField;

internal sealed class CoprimePrimeSumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coprime Prime Sum.",
        H("Coprime Prime Sum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-ideal-zeta-sum-unramified-coprime-div-log-tendsto-one"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/CoprimePrimeSum.primeIdealZetaSum_unramified_coprime_div_log_tendsto_one"),
                H("Coprime Prime Sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The coprime-norm-unramified prime sum is asymptotic to log(1/(s-1)): it differs from " +
                    "the universal prime sum (primeIdealZetaSum_univ_tendsto_log) by the finitely many " +
                    "excluded primes — ramified or with norm not coprime to m — whose bounded contribution " +
                    "is negligible against log → ∞."))),
                DescribeRole.Theorem)
        )));
}
