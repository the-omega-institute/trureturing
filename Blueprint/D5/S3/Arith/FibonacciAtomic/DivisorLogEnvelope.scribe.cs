using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class DivisorLogEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/DivisorLogEnvelope.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Moebius logarithmic divisor sum has a sharp positive envelope.",
        H("The Divisor Logarithmic Envelope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-divisor-log-sum"),
                DeclarationHandle.Create(Prefix + "moebiusLogSum"),
                H("The actual signed divisor sum"),
                StatementSource.FromAuthor(SumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural number R and real parameter t, "
                    + "S(R,t) is the finite sum over Nat.divisors R, denoted "
                    + "divisors(R) in the formula. For positive R these "
                    + "are exactly its positive natural divisors. Each coefficient is "
                    + "the integer ArithmeticFunction.moebius value cast to the reals, "
                    + "and log is the natural real logarithm. Nat.divisors 0 is empty. "
                    + "The envelope below concerns positive R and 0 < t <= 2/5."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("full-log-envelope"),
                DeclarationHandle.Create(Prefix + "full_log_envelope"),
                H("Positivity, the upper bound, and exact equality"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural R and real t with R positive "
                        + "and 0 < t <= 2/5, the actual signed divisor sum is "
                        + "strictly positive and at most log(1+t). Equality holds if "
                        + "and only if R=1. Neither oddness nor squarefreeness is required; "
                        + "the squarefree odd case follows with the same sum, "
                        + "inequalities and equality condition.")),
                    Paragraph(Text("Put f(d)=log(1+t^d). The elementary inequalities "
                        + "u/(1+u) <= log(1+u) <= u for u>0 and the bound "
                        + "on the absolute Moebius coefficient by one control every "
                        + "finite signed tail supported on d>=k by t^k/(1-t). "
                        + "The proof embeds its support into a finite integer interval "
                        + "and bounds the corresponding geometric sum.")),
                    Paragraph(Text("After removing d=1, all divisors are at least "
                        + "two. Since t^2/(1-t) < t/(1+t) <= f(1), this tail "
                        + "cannot cancel the positive term f(1). If R>1, let p "
                        + "be its least prime divisor. Its coefficient is minus one. "
                        + "Every remaining divisor other than 1 and p exceeds p, "
                        + "so the remaining tail has absolute value at most "
                        + "t^(p+1)/(1-t) < t^p/(1+t^p) <= f(p). Thus the "
                        + "negative term at p gives S(R,t)<f(1). For R=1 the "
                        + "single divisor term is f(1).")),
                    Paragraph(Text("The squarefree odd specialization is the "
                        + "positive logarithmic envelope in Section 382.2 of "
                        + "Fibonacci Atomic Relation Generation. The finite-tail "
                        + "estimate and least-prime deficit give the stated "
                        + "envelope for every positive natural modulus."))),
                DescribeRole.Theorem))));

    private static Formula S(Formula r, Formula t) => Call("S", r, t);

    private static Formula SumFormula()
    {
        var r = F.Id("R"); var t = F.Id("t"); var d = F.Id("d");
        Formula divisors = Seq(d, InMacro, Call("divisors", r));
        Formula term = Seq(Call("mu", d), Cdot,
            Call("log", Seq(D(1), Plus, new Formula.Power(t, d))));
        return Disp(Seq(Forall, Sp, r, InMacro, Seq(Mathbb, Grp(F.Id("N"))), Comma,
            t, InMacro, Seq(Mathbb, Grp(F.Id("R"))), Comma,
            Equal(S(r, t), Seq(new Formula.Subscript(Sum, divisors), term))));
    }

    private static Formula ResultFormula()
    {
        var r = F.Id("R"); var t = F.Id("t");
        Formula log = Call("log", Seq(D(1), Plus, t));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, r, InMacro, Seq(Mathbb, Grp(F.Id("N"))), Comma,
                t, InMacro, Seq(Mathbb, Grp(F.Id("R"))), Comma),
            Seq(D(0), Lt, r, Land, D(0), Lt, t, Le,
                new Formula.Fraction(D(2), D(5)), Rightarrow),
            Seq(D(0), Lt, S(r, t), Land, S(r, t), Le, log, Land,
                Open, S(r, t), Eq, log, Leftrightarrow, Sp, r, Eq, D(1), Close)
        ]));
    }
}
