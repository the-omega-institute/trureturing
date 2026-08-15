using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ToySpectrum;

internal sealed class TwoBodyHeatSeparationDocument : IScribeDocumentDefinition
{
    private static Formula CZero() => Seq(F.Id("c"), Underscore, D(0));

    private static Formula Shift() => Seq(D(2), F.Id("t"), Sp, Minus, Sp, CZero());

    private static Formula Root() => Seq(Sqrt, Grp(Shift()));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "After its collision time, the two-body quadratic heat model has two distinct real "
        + "roots whose squared separation grows linearly with slope eight.",
        H("Two-Body Heat Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-body-heat-real-root-separation"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ToySpectrum/TwoBodyHeatSeparation."
                    + "two_body_heat_real_root_separation"),
                H("The split roots have squared separation eight t minus four c zero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, CZero(), Comma, Sp, F.Id("t"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Open, Frac, Grp(CZero()), Grp(D(2)), Sp, Lt, Sp, F.Id("t"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("roots")), Open,
                    Operatorname, Grp(F.Id("twoBodyHeatPolynomial")),
                    Open, CZero(), Comma, Sp, F.Id("t"), Close, Close,
                    Sp, Eq, Sp, OpenBrace, Root(), Comma, Sp, Minus, Root(), CloseBrace,
                    Sp, Land, Sp, Root(), Sp, Neq, Sp, Minus, Root(),
                    Sp, Land, Sp, Open, Root(), Sp, Minus, Sp,
                    Grp(Minus, Root()), Close, Caret, Grp(D(2)),
                    Sp, Eq, Sp, D(8), F.Id("t"), Sp, Minus, Sp, D(4), CZero()))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The heat parameter is c zero minus twice t. Once t is strictly greater "
                        + "than c zero divided by two, the existing quadratic-collision certificate "
                        + "identifies the roots as plus and minus the square root of two t minus c "
                        + "zero and proves that they are distinct.")),
                    Paragraph(Text(
                        "Mathlib's square-root square theorem then gives the exact squared gap "
                        + "eight t minus four c zero, so its post-collision slope is eight.")),
                    Paragraph(Text(
                        "This closes only the post-collision real-root and squared-separation clause "
                        + "of the source atom's two-body law. The gas computation, finite-extinction "
                        + "claim, zeta-zero interpretation, and physical-time interpretation are not "
                        + "formalized or claimed here."))),
                DescribeRole.Theorem)),
        []));
}
