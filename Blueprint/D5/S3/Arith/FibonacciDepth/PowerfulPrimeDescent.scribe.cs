using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciDepth;

internal sealed class PowerfulPrimeDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonclassical powerful Fibonacci value forces a powerful block at "
            + "the largest prime dividing its index, with the original WSS square condition.",
        H("Largest-Prime Descent for Powerful Fibonacci Counterexamples"),
        Blocks(Describe.Lean(
            DescribeId.Create("powerful-fibonacci-largest-prime-descent"),
            DeclarationHandle.Create(
                "D5/S3/Arith/FibonacciDepth/PowerfulPrimeDescent."
                    + "powerful_fibonacci_counterexample_descends"),
            H("An actual prime-index block carries every counterexample"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every positive natural m outside {1,2,6,12}, if Nat.fib m "
                        + "is Powerful in the existing PowerfulDivisorTransform sense, "
                        + "there exists a prime ell at least seven dividing m and "
                        + "dominating every prime divisor of m. Nat.fib ell is Powerful. "
                        + "Every prime p dividing Nat.fib ell is greater than ell and "
                        + "has p squared dividing Nat.fib at the signed Frobenius index: "
                        + "p-1 when legendreSym 5 p=1, and p+1 otherwise.")),
                Paragraph(Text(
                    "The proof uses the original Powerful predicate, actual natural "
                        + "Fibonacci numbers, actual prime factors and the current "
                        + "FibonacciRank owner. It first eliminates indices supported "
                        + "on two, three and five using the simple factors at indices "
                        + "5,8,9,25 and the proved prime-square transport theorem. "
                        + "The remaining index has a largest prime ell at least seven.")),
                Paragraph(Text(
                    "Strong Fibonacci divisibility shows that every prime p in "
                        + "F_ell has exact entry point ell. The existing Frobenius "
                        + "rank bound and prime parity force p>ell, so p does not "
                        + "divide m. Prime-square transport now carries repeated "
                        + "divisibility backwards from F_m to F_ell. The same rank "
                        + "bound and forward divisibility give the displayed WSS "
                        + "square condition at p's own signed index.")),
                Paragraph(Text(
                    "The counterexample is an antecedent, not an asserted witness. "
                        + "The conclusion concerns value-primes p, and does not assert "
                        + "that the index-prime ell is WSS. No perfect-power "
                        + "classification, abc hypothesis, independent valuation "
                        + "formula, or supplied powerful prime block is assumed."))),
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
    private static Formula ExN(string name, Formula body) => Seq(
        Exists, Sp, V(name), Sp, InMacro, Sp, Seq(Mathbb, Grp(V("N"))), Comma, Sp, body);
    private static Formula And(params Formula[] xs)
    {
        var result = xs[^1];
        for (var i = xs.Length - 2; i >= 0; --i) { result = C("And", xs[i], result); }
        return result;
    }
    private static Formula Fib(Formula x) => C("Nat.fib", x);
    private static Formula Powerful(Formula x) => C("Powerful", x);
    private static Formula Dvd(Formula x, Formula y) => Seq(x, Sp, Mid, Sp, y);
    private static Formula Ne(Formula x, Formula y) => Seq(x, Sp, Neq, Sp, y);

    private static Formula Statement()
    {
        var m = V("m");
        var ell = V("ell");
        var p = V("p");
        var q = V("q");
        var excluded = And(Ne(m, V("1")), Ne(m, V("2")), Ne(m, V("6")), Ne(m, V("12")));
        var hypothesis = And(C("Lt", V("0"), m), Powerful(Fib(m)), excluded);
        var largest = AllN("q", C("Implies", C("Nat.Prime", q),
            C("Implies", Dvd(q, m), C("Le", q, ell))));
        var signedIndex = C("ite", C("Eq", C("legendreSym", V("5"), p), V("1")),
            C("Nat.sub", p, V("1")), C("add", p, V("1")));
        var allFactors = AllN("p", C("Implies", C("Nat.Prime", p),
            C("Implies", Dvd(p, Fib(ell)), And(C("Lt", ell, p),
                Dvd(new Formula.Power(p, V("2")), Fib(signedIndex))))));
        var target = And(C("Nat.Prime", ell), C("Le", V("7"), ell),
            Dvd(ell, m), largest, Powerful(Fib(ell)), allFactors);
        return Disp(AllN("m", C("Implies", hypothesis, ExN("ell", target))));
    }
}
