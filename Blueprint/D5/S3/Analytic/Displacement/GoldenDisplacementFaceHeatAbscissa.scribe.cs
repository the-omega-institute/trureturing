using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Displacement;

internal sealed class GoldenDisplacementFaceHeatAbscissaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonnegative Euler bridge promotes summable positive prime-power tails to a global sum, and collapses the expansion-face heat window to the exact golden abscissa.",
        H("The Exact Golden Displacement Face Heat Abscissa"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("summable-prime-power-tails-give-a-global-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatAbscissa."
                        + "summable_of_summable_prime_power_tail"),
                H("Summable prime-power tails give a global sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("f"), Colon, Sp, Mathbb, Grp(F.Id("N")), Sp,
                    To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("f"), Open, D(0), Close, Eq, D(0), Comma, Sp,
                    F.Id("f"), Open, D(1), Close, Eq, D(1), Comma, Sp,
                    Forall, Sp, F.Id("n"), Comma, Sp, D(0), Leq, F.Id("f"), Open,
                    F.Id("n"), Close, Comma, Sp,
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("n"), Comma, Sp,
                    Operatorname, Grp(F.Id("Coprime")), Open, F.Id("m"), Comma, Sp,
                    F.Id("n"), Close, Sp, Rightarrow, Sp,
                    F.Id("f"), Open, F.Id("m"), Times, Sp, F.Id("n"), Close, Eq,
                    F.Id("f"), Open, F.Id("m"), Close, Times, Sp, F.Id("f"), Open,
                    F.Id("n"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("Summable")), Open, Open, F.Id("p"), Sp,
                    F.Text, Grp(F.Id("prime")), Comma, Sp, F.Id("k"), Close, Mapsto, Sp,
                    F.Id("f"), Open, F.Id("p"), Caret,
                    Grp(F.Id("k"), Plus, D(1)), Close, Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("Summable")), Open, F.Id("f"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib's smooth-number Euler theorem computes every finite prime partial product. Nonnegativity turns the combined positive prime-power tail sum into a uniform exponential bound for those partial products, while every positive natural eventually lies in a smooth-number set. Bounded monotone finite sums therefore give global summability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-face-heat-abscissa-is-exactly-one-over-phi-squared"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatAbscissa."
                        + "faceLength_heat_abscissa_exact"),
                H("The face heat abscissa is exactly one over phi squared"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsHeatAbscissa")), Open,
                    F.Id("faceLength"), Comma, Sp,
                    Frac, Grp(D(1)), Grp(Varphi, Caret, Grp(D(2))), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Above one over phi squared, the frozen golden-spectrum theorem makes the complete positive prime-power tail summable. The bridge then sums the real displacement coefficients globally, and their closed form is the face heat family. The frozen face divergence theorem supplies the opposite half-plane, so the former bracket collapses to equality."))),
                DescribeRole.Theorem))));
}
