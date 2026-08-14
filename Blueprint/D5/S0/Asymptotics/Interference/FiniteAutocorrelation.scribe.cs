using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.Interference;

internal sealed class FiniteAutocorrelationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite Fourier sum has the exact pairwise autocorrelation expansion of its squared modulus.",
        H("Finite Autocorrelation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-fourier-sum-autocorrelation-expansion"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/Interference/FiniteAutocorrelation.finite_autocorrelation_normSq"),
                H("Finite Fourier sums expand into autocorrelation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("N"), Comma, Sp, F.Id("f"), Comma, Sp, F.Id("z"), Comma, Esc,
                    F.Id("normSq"), Open, F.Id("finiteSignal"), Open, F.Id("f"), Comma,
                    Sp, F.Id("z"), Close, Close, Eq, F.Id("finiteAutocorrelation"), Open,
                    F.Id("f"), Comma, Sp, F.Id("z"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any finite complex coefficient sequence and complex frequency, "
                        + "finiteSignal is the corresponding finite power sum and "
                        + "finiteAutocorrelation is its pairwise coefficient-conjugate expansion.")),
                    Paragraph(Text(
                        "The proof is a direct finite algebra calculation. Mathlib's conjugation "
                        + "homomorphism laws, star_pow, Complex.normSq_eq_conj_mul_self, and "
                        + "finite-sum product and reordering lemmas supply every step; no source "
                        + "instance facts are imported.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the leading identity clause of the "
                        + "source bundle. The coefficient specialization, diffraction formula, "
                        + "asymptotic peak law, zero-window statement, and corollary remain unresolved."))),
                DescribeRole.Theorem))));
}
