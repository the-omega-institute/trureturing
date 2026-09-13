using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibonacciPrimePowerPeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FibonacciPrimePowerPeriod.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The valuation of the actual first return determines the entire odd-prime period tower. "
            + "Separate finite seeds are consumed by unbounded formulas for two and five.",
        H("Complete Fibonacci Prime-Power Periods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-all-odd-prime-power-periods"),
                DeclarationHandle.Create(Prefix + "odd_prime_power_period"),
                H("Both plateau and growth regimes for every exponent"),
                StatementSource.FromAuthor(Tower()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For an odd prime p and every e>0, define "
                        + "s=padicValNat(p,gcd(F(period(p)),F(period(p)+1)-1)). "
                        + "Then period(p^e)=period(p)*p^(e-s), with natural subtraction. "
                        + "actual_initial_seed constructs phi^period(p)=1+p^s*B "
                        + "and proves p does not divide B. Thus s is the actual "
                        + "first-return depth, not an assumed plateau parameter.")),
                    Paragraph(Text("The proof covers hypothetical s>=2 without assuming "
                        + "Wall-Sun-Sun primes exist or do not exist. "
                        + "standard_quotient_zero_iff_depth proves that the standard "
                        + "signed-index quotient vanishes exactly when s>=2, away from 2 and 5. "
                        + "full_tower_of_standard_quotient_nonzero then fixes every higher period."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-dyadic-tower"),
                DeclarationHandle.Create(Prefix + "dyadic_period"),
                H("The dyadic tower starts from a depth-two seed"),
                StatementSource.FromAuthor(Call("Eq", Call("period", Call("power", F.Id("2"), F.Id("e"))),
                    Seq(F.Id("3"), Cdot, Call("power", F.Id("2"), Call("sub", F.Id("e"), F.Id("1")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every e>0, period(2^e)=3*2^(e-1). "
                        + "The proof verifies period(2)=3 and period(4)=6, then uses "
                        + "phi^6=1+4*(1+2*phi) in the stable depth-two regime. "
                        + "ramified_five_period similarly proves period(5^e)=20*5^(e-1) "
                        + "from the actual period-20 primitive defect. "
                        + "Neither exceptional characteristic is silently passed through "
                        + "the nonunit Frobenius-factor cancellation."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(xs[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }

    private static Formula Tower() => Disp(Seq(
        Call("period", Call("power", F.Id("p"), F.Id("e"))), Sp, Eq, Sp,
        Call("period", F.Id("p")), Cdot,
        Call("power", F.Id("p"), Call("sub", F.Id("e"), Call("initialDepth", F.Id("p"))))));
}
