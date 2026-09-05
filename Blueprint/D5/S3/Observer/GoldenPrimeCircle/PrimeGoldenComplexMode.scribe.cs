using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class PrimeGoldenComplexModeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/PrimeGoldenComplexMode.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "A first golden prime mode splits into prime-faithful heat amplitude "
                + "and recurrent unit-circle phase.",
            H("Prime Golden Complex Mode"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create(
                        "complex-mode-amplitude-phase-dichotomy"),
                    DeclarationHandle.Create(
                        Prefix + "complex_mode_amplitude_phase_dichotomy"),
                    H("Positive amplitude identifies primes while phase recurs"),
                    StatementSource.FromAuthor(AmplitudePhaseDichotomyFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The real coordinate controls modulus and the imaginary "
                                + "coordinate controls rotation.")),
                        Paragraph(Text(
                            "This is an analytic-time statement and does not identify "
                                + "the parameter with laboratory time."))),
                    DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula AmplitudePhaseDichotomyFormula()
    {
        Formula sigma = F.Id("s");
        Formula primes = F.Id("P");
        Formula epsilon = F.Id("e");
        Formula bound = F.Id("b");
        Formula phaseTime = F.Id("u");
        Formula time = F.Id("t");
        Formula prime = F.Id("p");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, sigma, Comma, Sp, D(0), Sp, Lt, Sp, sigma, Sp, Rightarrow, Sp,
            Forall, Sp, primes, Comma, Sp, Forall, Sp, epsilon, Comma, Sp,
            D(0), Sp, Lt, Sp, epsilon, Sp, Rightarrow, Sp,
            Forall, Sp, bound, Comma, Sp, Forall, Sp, phaseTime, Comma, RowBreak, Grp(),
            Call("Injective", Call("firstGoldenComplexMode", sigma, phaseTime)),
            Sp, Land, RowBreak, Grp(),
            Exists, Sp, time, Comma, Sp, bound, Sp, Lt, Sp, time, Sp, Land, Sp,
            Forall, Sp, prime, Sp, InMacro, Sp, primes, Comma, Sp,
            Call("norm", Seq(
                Call("firstGoldenComplexMode", D(0), time, prime), Sp, Minus, Sp, D(1))),
            Sp, Lt, Sp, epsilon, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
