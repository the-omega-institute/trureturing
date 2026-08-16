using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Limits;

internal sealed class HarmonicResidualLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized harmonic residual converges to one minus the Euler-Mascheroni constant.",
        H("Harmonic Residual Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("harmonic-residual-limit"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Limits/HarmonicResidualLimit."
                    + "harmonic_residual_tendsto_one_sub_euler_constant"),
                H("The harmonic residual tends to one minus Euler's constant"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                    OpenBracket, D(1), Sp, Minus, Sp,
                    Open, F.Id("H"), Underscore, F.Id("n"), Sp, Minus, Sp,
                    Log, Sp, F.Id("n"), Close, CloseBracket,
                    Sp, Eq, Sp, D(1), Sp, Minus, Sp, GammaLower, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H_n be the nth harmonic number. The pinned Mathlib theorem "
                        + "Real.tendsto_harmonic_sub_log proves that H_n - log n tends to "
                        + "the Euler-Mascheroni constant. Subtracting this convergent sequence "
                        + "from the constant sequence one gives the stated residual limit.")),
                    Paragraph(Text(
                        "This is partial closure of the source atom's asymptotic residual clause. "
                        + "It does not formalize the protocol-cost interpretation, tracking rates, "
                        + "or the other numerical and information-theoretic claims in that atom."))),
                DescribeRole.Theorem))));
}
