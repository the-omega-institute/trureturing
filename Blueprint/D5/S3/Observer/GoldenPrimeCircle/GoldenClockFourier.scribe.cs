using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenClockFourierDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenClockFourier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Reflection conjugates actual interval Fourier coefficients. "
                + "Power forgets direction, while cross coefficients cancel a common origin shift.",
            H("Golden Clock Fourier Observation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-clock-fourier-reflection"),
                    DeclarationHandle.Create(Prefix + "coefficient_reflect"),
                    H("An interval and its reflection have conjugate coefficients"),
                    StatementSource.FromAuthor(ReflectionFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For real angular frequency omega different from zero, "
                                + "coefficient(omega,a,b) is the actual interval integral "
                                + "of exp(-i*omega*x). The formula follows from the pinned "
                                + "mathlib integral_exp_mul_complex result.")),
                        Paragraph(Text(
                            "reflection_power_equal proves norm-square equality. "
                                + "cross_reflect_im proves sign reversal of the imaginary "
                                + "cross coefficient. It does not assume or claim that this "
                                + "imaginary part is nonzero at every frequency."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-clock-fourier-shared-origin"),
                    DeclarationHandle.Create(Prefix + "cross_common_translate"),
                    H("One common origin shift cancels in the cross coefficient"),
                    StatementSource.FromAuthor(TranslationFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The two measured intervals retain their labels and share "
                                + "the same shift t. The proof factors a unit-modulus "
                                + "complex exponential and cancels it with its conjugate.")),
                        Paragraph(Text(
                            "The module also proves no_common_center_translation for "
                                + "every distinct pair of golden resolutions. Its domain "
                                + "is the real representatives of the arc centers. "
                                + "Circle-quotient identifications and the infinite sampled "
                                + "pulse spectrum are separate obligations."))),
                    DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ReflectionFormula() => Disp(Seq(
        Call("coefficient", F.Id("omega"), Call("neg", F.Id("b")), Call("neg", F.Id("a"))),
        Sp, Eq, Sp,
        Call("conj", Call("coefficient", F.Id("omega"), F.Id("a"), F.Id("b")))));

    private static Formula TranslationFormula() => Disp(Seq(
        Call("cross", Call("shift", F.Id("t"), F.Id("z")),
            Call("shift", F.Id("t"), F.Id("w"))),
        Sp, Eq, Sp, Call("cross", F.Id("z"), F.Id("w"))));
}
