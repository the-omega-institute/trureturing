using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CompletionConstants;

internal sealed class GaussianSelfDualPiDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The standard real Fourier transform fixes a positive Gaussian exactly at scale pi.",
        H("Gaussian Fourier Self-Duality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gaussian-fourier-self-dual-scale-pi"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/CompletionConstants/GaussianSelfDualPi."
                    + "gaussian_self_dual_iff"),
                H("The positive Gaussian is strictly self-dual exactly at scale pi"),
                StatementSource.FromAuthor(SelfDualFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Fourier transform is Mathlib's standard real transform, whose kernel "
                        + "is exp(-2 pi i x xi). The real Gaussian is embedded into the complex "
                        + "codomain of that transform.")),
                    Paragraph(Text(
                        "At frequency zero, self-duality and the pinned Gaussian integral give "
                        + "sqrt(pi/a) = 1, hence a = pi because a is positive. Conversely, the "
                        + "pinned Fourier-Gaussian formula at unit normalized scale gives strict "
                        + "self-duality when a = pi."))),
                DescribeRole.Theorem))));

    private static Formula SelfDualFormula()
    {
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula gaussian = Seq(
            Open, x, Sp, Mapsto, Sp,
            Operatorname, Grp(F.Id("exp")), Open,
            Minus, a, Thin, x, Caret, Grp(D(2)), Close, Close);

        return Disp(Seq(
            Forall, Sp, a, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(0), Lt, a, Sp, Rightarrow, Sp,
            Open,
            Widehat, Grp(gaussian), Sp, Eq, Sp, gaussian,
            Sp, Iff, Sp, a, Sp, Eq, Sp, Pi,
            Close, Dot));
    }
}
