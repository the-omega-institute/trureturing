using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibonacciPrimeSquareLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FibonacciPrimeSquareLift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "The actual Fibonacci period at a prime square is either unchanged or "
                + "multiplied by that prime. Exact integer quotients identify the first case.",
            H("Fibonacci Prime-Square Lift"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("fibonacci-prime-square-dichotomy"),
                    DeclarationHandle.Create(Prefix + "prime_square_period_dichotomy"),
                    H("There are exactly two possible period-lift outcomes"),
                    StatementSource.FromAuthor(Dichotomy()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every prime p, including 2 and 5, the statement concerns "
                                + "the actual least period already identified with the "
                                + "Fibonacci sequence in FibonacciReturnSpectrum. No "
                                + "period formula or nonexceptionality assumption is supplied.")),
                        Paragraph(Text(
                            "At an existing return t, write F(t)=p*a and F(t+1)=1+p*b. "
                                + "The matrix over ZMod(p^2) is I+p*B with "
                                + "B=[[b,a],[a,b-a]]. Its defect has square zero, so its "
                                + "p-th power is I. Divisibility of actual orders then "
                                + "forces the quotient of the two periods to be 1 or p."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("fibonacci-prime-square-quotients"),
                    DeclarationHandle.Create(Prefix + "square_period_eq_iff_quotients"),
                    H("The plateau is detected by two exact quotient residues"),
                    StatementSource.FromAuthor(QuotientCriterion()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For positive p, put r=period(p), a=F(r)/p and "
                                + "b=(F(r+1)-1)/p, using natural-number division. "
                                + "The existing return conditions prove both divisions "
                                + "exact. The period remains r at p^2 exactly when "
                                + "p divides both a and b.")),
                        Paragraph(Text(
                            "first_lift_matrix binds these quotients to the actual "
                                + "companion power, rather than assuming a lift matrix. "
                                + "This criterion and the dichotomy do not decide whether "
                                + "an exceptional Wall-Sun-Sun prime exists."))),
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

    private static Formula Dichotomy() => Disp(Call("Or",
        Seq(Call("period", Call("square", F.Id("p"))), Sp, Eq, Sp,
            Call("period", F.Id("p"))),
        Seq(Call("period", Call("square", F.Id("p"))), Sp, Eq, Sp,
            F.Id("p"), Cdot, Call("period", F.Id("p")))));

    private static Formula QuotientCriterion() => Disp(Call("Iff",
        Seq(Call("period", Call("square", F.Id("p"))), Sp, Eq, Sp,
            Call("period", F.Id("p"))),
        Call("And", Call("divides", F.Id("p"), F.Id("a")),
            Call("divides", F.Id("p"), F.Id("b")))));
}
