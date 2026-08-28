using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Limits;

internal sealed class EulerCountertermUniquenessDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Constants/Limits/EulerCountertermUniqueness.euler_counterterm_unique";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Euler-Mascheroni constant is the unique finite harmonic-log counterterm, "
            + "while pi eliminates the standard Gaussian Fourier self-duality defect.",
        H("Euler Counterterm Uniqueness and the Pi Contrast"),
        Blocks(Describe.Lean(
            DescribeId.Create("euler-counterterm-uniqueness"),
            DeclarationHandle.Create(Declaration),
            H("Gamma is the unique finite counterterm and pi removes the duality defect"),
            StatementSource.FromAuthor(ContractFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here H_n is the nth harmonic number. Pinned Mathlib proves that H_n minus "
                        + "log n tends to the Euler-Mascheroni constant, which supplies the "
                        + "zero-residual certificate. Adding any candidate counterterm back to "
                        + "its zero-residual limit and using uniqueness of real limits identifies "
                        + "that candidate with gamma. Both source occurrences of this conditional "
                        + "uniqueness are displayed separately.")),
                Paragraph(Text(
                    "For the source's pi contrast, g_a is exp(-a x^2), the Fourier transform is "
                        + "Mathlib's standard real transform with kernel exp(-2 pi i x xi), and "
                        + "the named defect is the transform of g_a minus g_a. The repository's "
                        + "Gaussian self-duality theorem proves that this defect vanishes at pi; "
                        + "the theorem does not replace the Fourier structure by a scalar proxy."))),
            DescribeRole.Theorem))));

    private static Formula ContractFormula()
    {
        Formula c = F.Id("c");
        Formula n = F.Id("n");
        Formula gammaResidual = ResidualLimit(GammaLower, n);
        Formula uniqueness = Seq(
            Forall, Sp, c, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            OpenBracket, ResidualLimit(c, n), CloseBracket, Sp, Implies, Sp,
            c, Sp, Eq, Sp, GammaLower);
        Formula gaussianPi = Seq(F.Id("g"), Underscore, Pi);
        Formula piEliminates = Seq(
            Widehat, Grp(gaussianPi), Sp, Minus, Sp, gaussianPi, Sp, Eq, Sp, D(0));

        return Disp(Seq(
            OpenBracket, uniqueness, CloseBracket, Sp, Land, RowBreak, Grp(),
            OpenBracket, gammaResidual, CloseBracket, Sp, Land, RowBreak, Grp(),
            OpenBracket, uniqueness, CloseBracket, Sp, Land, RowBreak, Grp(),
            OpenBracket, piEliminates, CloseBracket, Dot));
    }

    private static Formula ResidualLimit(Formula counterterm, Formula n) => Seq(
        Lim, Underscore, Grp(n, To, Infty), Sp,
        Open, F.Id("H"), Underscore, n, Sp, Minus, Sp,
        Log, Sp, n, Sp, Minus, Sp, counterterm, Close,
        Sp, Eq, Sp, D(0));
}
