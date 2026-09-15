using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciDepth;

internal sealed class PrimeSquareTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An extra prime factor at a Fibonacci multiple index has exactly two causes: "
            + "an already repeated value-prime, or a multiplier divisible by that prime.",
        H("Exact Prime-Square Transport in the Fibonacci Recurrence"),
        Blocks(Describe.Lean(
            DescribeId.Create("fibonacci-prime-square-multiple-iff"),
            DeclarationHandle.Create(
                "D5/S3/Arith/FibonacciDepth/PrimeSquareTransport.prime_square_fib_mul_iff"),
            H("The square-factor alternative at every multiple index"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For all natural p,n,k, assume p is prime, n is positive and p "
                        + "divides Nat.fib n. Then p squared divides Nat.fib(n*k) "
                        + "if and only if p squared already divides Nat.fib n or p "
                        + "divides k. The prime two and multiplier zero are included. "
                        + "There is no hypothesis that the initial valuation is one.")),
                Paragraph(Text(
                    "The proof derives both recurrence coordinates modulo p squared. "
                        + "Writing f=F_n and g=F_(n+1), the coefficient ring has f^2=0. "
                        + "Induction gives F_(n*(k+1))=(k+1)*f*g^k and "
                        + "F_(n*(k+1)+1)=g^(k+1). Consecutive Fibonacci coprimality "
                        + "permits cancellation of g^k. Cancelling one factor p in "
                        + "the integers then gives the stated prime-product alternative.")),
                Paragraph(Text(
                    "This is the square-divisibility portion of the classical "
                        + "Fibonacci valuation theory. The script proves it from "
                        + "Nat.fib and elementary ring arithmetic rather than assuming "
                        + "a valuation-lifting theorem or a rank formula modulo p squared. "
                        + "Its public conclusion distinguishes automatic index lifting "
                        + "from repeated divisibility at the starting value."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] xs)
    {
        var terms = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i > 0) { terms.Add(Comma); terms.Add(Sp); }
            terms.Add(xs[i]);
        }
        terms.Add(Close);
        return Seq([.. terms]);
    }
    private static Formula AllN(string name, Formula body) => Seq(
        Forall, Sp, V(name), Sp, InMacro, Sp, Seq(Mathbb, Grp(V("N"))), Comma, Sp, body);
    private static Formula Square(Formula x) => new Formula.Power(x, V("2"));
    private static Formula Fib(Formula x) => C("Nat.fib", x);
    private static Formula Dvd(Formula x, Formula y) => Seq(x, Sp, Mid, Sp, y);

    private static Formula Statement()
    {
        var p = V("p");
        var n = V("n");
        var k = V("k");
        var assumptions = C("And", C("Nat.Prime", p),
            C("And", C("Lt", V("0"), n), Dvd(p, Fib(n))));
        var conclusion = C("Iff", Dvd(Square(p), Fib(C("mul", n, k))),
            C("Or", Dvd(Square(p), Fib(n)), Dvd(p, k)));
        return Disp(AllN("p", AllN("n", AllN("k", C("Implies", assumptions, conclusion)))));
    }
}
