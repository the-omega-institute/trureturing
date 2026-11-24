using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class EvenHarmonicFirstMomentDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/EvenHarmonicFirstMoment";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive vanishing even harmonics give a sharp first harmonic bound.",
        H("The first harmonic with vanishing even moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sharp-first-harmonic-even-block"),
                DeclarationHandle.Create(Owner + ".sharp_first_harmonic_even_block"),
                H("The attained first harmonic bound"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let N be a positive integer. Write P for finite laws on complex unit "
                        + "phases with nonnegative weights summing to one, and P with subscript N "
                        + "for such laws on N indexed phases. The moment m with index h averages "
                        + "the h-th powers of the phases. The bound B with subscript N is the "
                        + "reciprocal of N times sin(pi/(2N)).")),
                    Paragraph(Text(
                        "Rotate the phases so that the first moment is nonnegative real. "
                        + "For y the squared real projection, 2y−1 is the real part of the "
                        + "second power of the phase. Chebyshev polynomials of degrees below N "
                        + "then express the polynomial means in terms of the prescribed even moments.")),
                    Paragraph(Text(
                        "The polynomial R(y)=1+(-1)^N T_N(2y−1) is nonnegative on [0,1] "
                        + "and positive at each negative argument. It vanishes on the squared "
                        + "real projections of the attaining phases. For s>0, the numerator "
                        + "y+s R(y)/R(-s) vanishes at -s, so division by y+s gives a polynomial "
                        + "of degree below N. That polynomial majorizes y/(y+s), with equality "
                        + "at the attaining projections. Integrating the comparison at s=t² "
                        + "over real t gives the bound on the square-root mean.")),
                    Paragraph(Text(
                        "Use uniform weights at the phases exp(i pi (j−(N−1)/2)/N) for "
                        + "j=0 through N−1. Their squares form an equally spaced set and "
                        + "character averaging gives the required vanishing moments. The real "
                        + "first moment is evaluated by telescoping the sine differences at "
                        + "the ends of equally spaced intervals."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var law = F.Id("L");
        var size = F.Id("N");
        var index = F.Id("k");
        var laws = Seq(Mathcal, Grp(F.Id("P")));
        var bound = new Formula.Subscript(F.Id("B"), size);
        var first = new Formula.Absolute(Moment(D(1)));
        var vanish = Parenthesized(Seq(Forall, Sp, D(0), Sp, Lt, Sp, index, Sp, Lt, Sp, size,
            Comma, Sp, Moment(Multiply(D(2), index)), Sp, Eq, Sp, D(0)));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, law, Sp, InMacro, Sp, laws, Comma, Sp,
                Parenthesized(Seq(vanish, Sp, Implies, Sp, first, Sp, Leq, Sp, bound))),
            Seq(Exists, Sp, law, Sp, InMacro, Sp, new Formula.Subscript(laws, size), Comma, Sp,
                Parenthesized(Seq(vanish, Sp, Land, Sp, first, Sp, Eq, Sp, bound)))]));
    }

    private static Formula Moment(Formula index) =>
        Seq(new Formula.Subscript(F.Id("m"), index), Parenthesized(F.Id("L")));

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
}
