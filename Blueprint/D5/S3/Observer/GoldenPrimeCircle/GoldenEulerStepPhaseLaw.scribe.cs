using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenEulerStepPhaseLawDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenEulerStepPhaseLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Deterministic Zeckendorf long-short steps become a two-letter "
                + "Euler phase alphabet in each prime channel.",
            H("Golden Euler Step Phase Law"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("prime-step-phase-euler"),
                    DeclarationHandle.Create(Prefix + "prime_step_phase_euler"),
                    H("Each deterministic step obeys Euler's formula"),
                    StatementSource.FromAuthor(EulerStepPhaseFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Zeckendorf chooses the phi or phi-squared frequency "
                                + "increment before the phase is evaluated.")),
                        Paragraph(Text(
                            "Scalar unit-circle multiplication forgets adjacent "
                                + "step order, exposing an endpoint chronology "
                                + "obstruction."))),
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

    private static Formula EulerStepPhaseFormula()
    {
        Formula time = F.Id("t");
        Formula prime = F.Id("p");
        Formula layer = F.Id("v");
        Formula angle = Seq(time, Sp, Cdot, Sp, Call("primeStepFrequency", prime, layer));
        return Disp(Seq(
            Forall, Sp, time, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Forall, Sp, prime, Colon, Sp, F.Id("Nat"), Dot, F.Id("Primes"), Comma, Sp,
            Forall, Sp, layer, Colon, Sp, F.Id("Nat"), Comma, Sp,
            Call("primeStepPhase", time, prime, layer), Sp, Eq, Sp,
            Call("cos", angle), Sp, Plus, Sp,
            Call("sin", angle), Sp, Cdot, Sp, F.Id("i"), Dot));
    }
}
