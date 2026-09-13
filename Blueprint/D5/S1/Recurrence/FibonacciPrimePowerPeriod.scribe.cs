using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibonacciPrimePowerPeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FibonacciPrimePowerPeriod.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual first return determines the entire odd-prime period tower and the depth "
            + "of every repeated return. Separate seeds cover two and five.",
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
                        + "and proves p does not divide B. The depth is obtained from "
                        + "the actual return, not supplied as a plateau assumption.")),
                    Paragraph(Text("Hypothetical s>=2 is included. The standard signed-index "
                        + "quotient vanishes exactly when s>=2, away from 2 and 5. "
                        + "A nonzero standard quotient therefore determines every higher period."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-return-content-depth-growth"),
                DeclarationHandle.Create(Prefix + "returnContent_multiple_valuation"),
                H("Every positive time multiplier has an exact return depth"),
                StatementSource.FromAuthor(DepthGrowth()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For an odd prime p, r=period(p), and every natural k>0, "
                        + "the valuation of C(r*k) is initialDepth(p)+padicValNat(p,k), "
                        + "where C(t)=gcd(F(t),F(t+1)-1). This follows from the proved "
                        + "period tower and the original return-content equivalence.")),
                    Paragraph(Text("returnContent_multiple_power_dvd first proves, for every "
                        + "e>0, that p^e divides C(r*k) exactly when p^(e-s) divides k. "
                        + "That divisibility statement includes k=0. The valuation theorem "
                        + "excludes k=0 because padicValNat uses a finite default at zero. "
                        + "The proof establishes divisibility at s+v_p(k) and its failure "
                        + "at the next level, so it gives equality rather than a lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-dyadic-tower"),
                DeclarationHandle.Create(Prefix + "dyadic_period"),
                H("The dyadic tower starts from a depth-two seed"),
                StatementSource.FromAuthor(Dyadic()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every e>0, period(2^e)=3*2^(e-1). The proof uses "
                        + "period(2)=3, period(4)=6, and phi^6=1+4*(1+2*phi). "
                        + "ramified_five_period proves period(5^e)=20*5^(e-1) from the "
                        + "actual period-20 primitive defect. Neither exceptional "
                        + "characteristic is passed through a nonunit cancellation."))),
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

    private static Formula DepthGrowth() => Disp(Seq(
        Call("valuation", F.Id("p"), Call("C", Seq(F.Id("r"), Cdot, F.Id("k")))),
        Sp, Eq, Sp, Call("initialDepth", F.Id("p")), Plus,
        Call("valuation", F.Id("p"), F.Id("k"))));

    private static Formula Dyadic() => Disp(Seq(
        Call("period", Call("power", F.Id("2"), F.Id("e"))), Sp, Eq, Sp,
        F.Id("3"), Cdot, Call("power", F.Id("2"), Call("sub", F.Id("e"), F.Id("1")))));
}
