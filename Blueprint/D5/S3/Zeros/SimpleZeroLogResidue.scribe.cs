using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class SimpleZeroLogResidueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Zeros/SimpleZeroLogResidue",
            "A simple analytic zero has unit normalized logarithmic residue."),
        H("Simple-Zero Logarithmic Residue"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("simple-zero-has-unit-logarithmic-residue"),
                H("A simple zero has unit logarithmic residue"),
                LeanTheorem(
                    "D5/S3/Zeros/SimpleZeroLogResidue."
                    + "simple_zero_has_unit_logarithmic_residue"),
                Disp(Seq(
                    Lim, Underscore,
                    Grp(F.Id("z"), Sp, To, Sp, F.Id("z"), Underscore, D(0)),
                    Sp, Open, F.Id("z"), Sp, Minus, Sp,
                    F.Id("z"), Underscore, D(0), Close, Sp,
                    Operatorname, Grp(F.Id("logDeriv")), Open, F.Id("f"), Close,
                    Open, F.Id("z"), Close, Sp, Eq, Sp, D(1))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let f be complex analytic at z_0, with f(z_0) = 0 and nonzero "
                        + "derivative there. Then (z - z_0) times the logarithmic "
                        + "derivative of f tends to one as z approaches z_0 away from "
                        + "the center. Thus a simple zero contributes unit local residue, "
                        + "the analytic invariant behind one full phase winding.")),
                    Paragraph(Text(
                        "This declaration is a thin wrapper around mathlib's "
                        + "AnalyticAt.tendsto_mul_logDeriv_simple_zero. The source atom's "
                        + "finite numerical phase difference is not reproduced as an exact "
                        + "equality; the theorem records the stronger general local law that "
                        + "explains that reading.")))
            ))));
}
