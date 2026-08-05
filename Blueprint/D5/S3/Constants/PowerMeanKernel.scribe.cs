using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class PowerMeanKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S3/Constants/PowerMeanKernel",
                "Five discrete power means define the rationalizable symmetric metric kernels."),
            H("Power Mean Kernels"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("half-power-average"),
                    H("The half-power mean is an average"),
                    LeanTheorem(
                        "D5/S3/Constants/PowerMeanKernel.meanHalf_eq_average"),
                    Disp(Seq(
                        F.Id("M"), Underscore, Frac, Grp(D(1)), Grp(D(2)),
                        Grp(F.Id("a"), Comma, F.Id("b")), Eq,
                        Frac,
                        Grp(F.Id("M"), Underscore, D(0), Grp(F.Id("a"), Comma, F.Id("b")), Plus,
                            F.Id("M"), Underscore, D(1), Grp(F.Id("a"), Comma, F.Id("b"))),
                        Grp(D(2)), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "For nonnegative a and b, expanding the square in the half-power "
                            + "mean and using sqrt(a b) = sqrt(a) sqrt(b) gives the identity.")),
                        Paragraph(Text(
                            "The same Lean module defines the parameters -1, -1/2, 0, 1/2, and 1, "
                            + "together with the symmetric metric-kernel conversion "
                            + "k(t) = 2 / M(1+t, 1-t). It also proves the harmonic and arithmetic "
                            + "symmetric-input reductions. Exact integral evaluations and the "
                            + "completeness of the genus-zero parameter list are outside this "
                            + "algebraic theorem's scope.")))
                ))));
}
