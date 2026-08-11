using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class MoranComplexDimensionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S3/Constants/MoranComplexDimensions",
                "The equal-ratio Moran dimension extends to a log-periodic ladder of complex solutions."),
            H("Equal-Ratio Moran Complex Dimensions"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("the-moran-equation-holds-on-the-complex-dimension-ladder"),
                    H("The Moran equation holds on the complex dimension ladder"),
                    LeanTheorem(
                        "D5/S3/Constants/MoranComplexDimensions.moran_complex_dimension"),
                    Disp(Seq(
                        F.Id("D"), Eq,
                        Frac,
                        Grp(Log, Sp, F.Id("M")),
                        Grp(F.Id("k"), Sp, Log, Sp, Varphi),
                        Comma, Qquad, Sp,
                        F.Id("s"), Underscore, Grp(F.Id("n")), Eq, F.Id("D"), Plus,
                        Frac,
                        Grp(D(2), Pi, Sp, F.Id("i"), Sp, F.Id("n")),
                        Grp(F.Id("k"), Sp, Log, Sp, Varphi),
                        Comma, Quad, Sp,
                        F.Id("n"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Qquad, Sp,
                        F.Id("M"), Cdot, Varphi, Caret,
                        Grp(Minus, F.Id("k"), F.Id("s"), Underscore, Grp(F.Id("n"))),
                        Eq, D(1), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "For positive natural M and k and real phi greater than one, the real "
                            + "Moran dimension is log M divided by k log phi. Adding each integer "
                            + "multiple of 2 pi i divided by k log phi leaves the complexified "
                            + "equal-ratio Moran equation unchanged, producing its log-periodic "
                            + "tower of solutions.")))
                ))));
}
