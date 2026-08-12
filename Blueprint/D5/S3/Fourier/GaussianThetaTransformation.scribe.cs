using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class GaussianThetaTransformationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive-real Gaussian theta sum transforms by reciprocal scaling.",
        H("Gaussian Theta Transformation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-positive-real-gaussian-theta-sum-transforms-by-reciprocal-scaling"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/GaussianThetaTransformation.gaussian_theta_transformation"),
                H("The Gaussian theta sum transforms by reciprocal scaling"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("t"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    D(0), Lt, F.Id("t"), Sp, Rightarrow, Sp,
                    Sum, Underscore, Grp(F.Id("n"), InMacro, Mathbb, Grp(F.Id("Z"))),
                    Operatorname, Grp(F.Id("exp")), Open,
                    Minus, Pi, Thin, F.Id("t"), Thin, F.Id("n"), Caret, Grp(D(2)), Close,
                    Sp, Eq, Sp,
                    F.Id("t"), Caret, Grp(Minus, Frac, Grp(D(1)), Grp(D(2))),
                    Sum, Underscore, Grp(F.Id("n"), InMacro, Mathbb, Grp(F.Id("Z"))),
                    Operatorname, Grp(F.Id("exp")), Open,
                    Minus, Pi, Thin, F.Id("t"), Caret, Grp(Minus, D(1)), Thin,
                    F.Id("n"), Caret, Grp(D(2)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive real t, the sum over all integers n of exp(-pi t n^2) "
                    + "equals t^(-1/2) times the same sum with t replaced by 1/t. Pinned "
                    + "Mathlib proves exactly this real Gaussian transformation using Poisson "
                    + "summation, so the Lean declaration is a thin repository-addressed wrapper."))),
                DescribeRole.Theorem))));
}
