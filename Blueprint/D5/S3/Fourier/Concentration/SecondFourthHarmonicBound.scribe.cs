using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class SecondFourthHarmonicBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/SecondFourthHarmonicBound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second and fourth harmonic bounds give an attained bound on the first harmonic.",
        H("A sharp bound from the second and fourth harmonics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sharp-second-fourth-harmonic-bound"),
                DeclarationHandle.Create(Owner + ".sharp_second_fourth_harmonic_bound"),
                H("The largest first harmonic for two prescribed caps"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a finite family of unit phases and one set of nonnegative real "
                        + "weights summing to one. The moments m₁, m₂, and m₄ are the weighted "
                        + "first, second, and fourth powers. The caps e and k lie in [0,1]. "
                        + "Put b=min(e,sqrt((1+k)/2)) and r=(1+b)/2. For b=1 the bound B "
                        + "is one. For b<1 put a=min(sqrt(r),sqrt((1+k)/(4(1−b)))) and "
                        + "B=(a+r)/(1+a). The upper bound is attained with at most three phases.")),
                    Paragraph(Text(
                        "Rotate the phases so that the first moment is nonnegative real. "
                        + "For the real projections x the second cap and the fourth cap give "
                        + "an upper bound r on the mean of x². In the branch a=sqrt(r), "
                        + "the weighted Cauchy–Schwarz inequality gives B. In the other branch "
                        + "the fourth harmonic bounds the mean of x²−x⁴. The pointwise "
                        + "quartic comparison with remainder (1−x)(x−a)²(x+1+2a) then "
                        + "bounds the mean of x.")),
                    Paragraph(Text(
                        "For b<1 the attaining law puts weight (r−a²)/(1−a²) at 1 and "
                        + "splits the remaining weight between conjugate unit phases with real "
                        + "part a. The third phase is dispensable whenever its weight is zero. "
                        + "For b=1 take a point mass. In particular the bound for e=k=0 is 2/3."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var first = Magnitude(1);
        var condition = Seq(Magnitude(2), Sp, Leq, Sp, F.Id("e"), Sp, Land, Sp,
            Magnitude(4), Sp, Leq, Sp, F.Id("k"));
        return Disp(Seq(condition, Sp, Implies, Sp, first, Sp, Leq, Sp, F.Id("B")));
    }

    private static Formula Magnitude(int mode) =>
        new Formula.Absolute(new Formula.Subscript(F.Id("m"), D(mode)));
}
