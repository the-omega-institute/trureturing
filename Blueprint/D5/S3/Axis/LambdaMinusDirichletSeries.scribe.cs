using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class LambdaMinusDirichletSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The contraction-face Dirichlet series splits into zeta and a prime-axis factor.",
        H("Contraction-Face Dirichlet Series"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lambda-minus-dirichlet-series"),
                DeclarationHandle.Create(
                    "D5/S3/Axis/LambdaMinusDirichletSeries."
                        + "lambda_minus_dirichlet_series"),
                H("The contraction-face series has a diagonal prime-axis decomposition"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Operatorname, Grp(F.Id("Re")), Open, F.Id("s"), Close,
                    Sp, Gt, Sp, D(1), Comma, RowBreak,
                    Sum, Underscore, Grp(F.Id("n"), Sp, Geq, Sp, D(1)),
                    F.Id("lambdaMinus"), Open, F.Id("n"), Close,
                    F.Id("n"), Caret, Grp(Minus, F.Id("s")),
                    Sp, Eq, Sp,
                    Zeta, Open, F.Id("s"), Close, Thin, F.Id("H"), Open, F.Id("s"), Close,
                    Comma, RowBreak,
                    F.Id("H"), Open, F.Id("s"), Close, Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("p"), Sp, F.Text, Grp(F.Id("prime"))),
                    Operatorname, Grp(F.Id("log")), Open, F.Id("p"), Close,
                    Open, D(1), Minus, F.Id("p"), Caret, Grp(Minus, F.Id("s")), Close,
                    Sum, Underscore, Grp(F.Id("v"), Sp, Geq, Sp, D(1)),
                    F.Id("betaContraction"), Open, F.Id("v"), Close,
                    F.Id("p"), Caret, Grp(Minus, F.Id("v"), F.Id("s")),
                    Comma, RowBreak,
                    Forall, Sp, F.Id("v"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Lvert, Sp, F.Id("betaContraction"), Open, F.Id("v"), Close, Sp, Rvert,
                    Sp, Lt, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The repository contraction reading is additive on coprime inputs. "
                            + "Its one-step prime-power differences form an arithmetic function "
                            + "supported on prime powers, and divisor summation recovers lambdaMinus.")),
                    Paragraph(Text(
                        "Mathlib's convolution theorem supplies the zeta factor. Its exact "
                            + "prime-power support reindexing theorem turns the remaining L-series "
                            + "into a sum over primes and positive exponents; a convergent telescoping "
                            + "identity gives the displayed local factor.")),
                    Paragraph(Text(
                        "The existing radical bound applied to powers of two gives the strict unit "
                            + "window for every betaContraction exponent. No finite truncation or "
                            + "numerical certificate is used."))),
                DescribeRole.Theorem))));
}
